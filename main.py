"""AstrBot 插件：用你自己的 RVC 音色唱整首歌。

踩过的坑（2026-11-20）：
  1. 选歌别用 SessionWaiter。register_wait() 不会把 filter 登记进全局
     FILTERS（那是 @session_waiter 装饰器干的），插件一重载更是全丢，
     用户回的「5」会漏给大模型，它自己乱调 sing_song。现在用 _pending
     + @filter.regex(纯数字) 自己接。
  2. Record.convert_to_base64() 写死 target_format="wav"，mp3 会被重编码成
     48kHz 立体声。4 分半的歌 base64 后约 68MB，QQ 发不出去。
     解法：别用 Record，走 _send_audio() 用 MediaResolver(preserve_mp3=True)
     直接拿 mp3 原始字节拼 onebot 段 —— 4.26MB 的 mp3 只有 5.68MB base64，
     音质零损失。降采样是下策（32kHz 单声道 22.7MB，听着发闷）。
  3. 歌曲海的 ID3 标签不可信（张靓颖版里写的是「华语群星」），但音源是对的，
     别拿标签去校验歌手。

链路：
    歌名 -> 歌曲海搜歌 -> 下载原曲 -> rvc-next 分离人声 -> 换成她的音色
         -> 和伴奏混回 -> Record 语音发给对方

为什么要在后台跑：一首歌的分离 + 换声要 60~160 秒，同步等会让整条消息链
卡死、还可能触发平台超时。所以指令只负责「受理」，真正干活的是 asyncio 任务，
完成后用 context.send_message 主动投递。
"""

from __future__ import annotations

import asyncio
import html as html_lib
import json
import os
import re
import shutil
import tempfile
import time
from pathlib import Path

import aiohttp

from astrbot.api import logger
from astrbot.api.event import AstrMessageEvent, MessageChain, filter
from astrbot.api.message_components import Plain, Record
from astrbot.api.platform import MessageType
from astrbot.core.platform.message_session import MessageSesion
from astrbot.core.utils.media_utils import MediaResolver
from astrbot.api.star import Context, Star, register

PLUGIN_NAME = "astrbot_plugin_sing"
SHARED_VOICE_FILE = "voice_shared.json"
DEFAULT_WORKDIR = Path(r"D:\GAME\Codex++Ollama\RVC\sing\downloads")
DEFAULT_OUTDIR = Path(r"D:\GAME\Codex++Ollama\RVC\sing\output_sing")


class _EventStub:
    """选歌时原事件已经结束，但 _run_sing 只需要 umo，用这个顶上。"""

    def __init__(self, umo: str) -> None:
        self.unified_msg_origin = umo

GEQUHAI = "https://www.gequhai.com"
GDSTUDIO = "https://music-api.gdstudio.xyz/api.php"
BROWSER_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/120.0 Safari/537.36"
)

# 显存不够时的降级顺序（越往后越轻）
PRESET_FALLBACK = ["karaoke", "vocals-aggressive", "dereverb"]

_SEARCH_ROW = re.compile(
    r'href="/play/(\d+)"[^>]*>\s*([^<]+?)\s*</a>\s*</td>\s*<td[^>]*>([^<]*)</td>',
    re.S,
)

HELP_TEXT = """唱歌指令：
/唱歌 <歌名> —— 搜到多个版本会列出来让你选
/唱歌 <歌名> <歌手> —— 直接指定版本，例如 /唱歌 心湖 张靓颖
/唱歌 <歌名> 重唱 —— 换过音色想重唱，加「重唱」就不吃旧成品
/点歌 <歌名> —— 同上
/唱歌列表 <歌名> —— 只搜不唱，看看有哪些版本
/唱歌状态 —— 看服务是否就绪
/唱歌帮助 —— 就是这段话
/发歌 —— 把成品目录里最新的一首重发一遍（测发送用）

选歌时回数字（1~N）挑版本，回「取消」放弃。90 秒不回就作废。
也可以直接跟她说「唱首歌给我听」，模型会自己调用。"""


@register(
    PLUGIN_NAME,
    "cyrene",
    "用你自己的 RVC 音色唱整首歌",
    "1.0.0",
    "",
)
class SingPlugin(Star):
    """点歌 -> 后台生成 -> 主动投递语音。"""

    def __init__(self, context: Context, config: dict | None = None):
        super().__init__(context)
        self.config: dict = dict(config or {})
        # 原音频放 D 盘，别占 C 盘；配置里 download_dir 可覆盖
        self._workdir = Path(
            str(self._cfg("download_dir", "") or "").strip()
            or DEFAULT_WORKDIR
        )
        self._outdir = Path(
            str(self._cfg("output_dir", "") or "").strip() or DEFAULT_OUTDIR
        )
        try:
            self._outdir.mkdir(parents=True, exist_ok=True)
        except OSError:
            logger.warning("[sing] 成品目录不可用，成品留在 rvc 输出目录")
            self._outdir = None
        try:
            self._workdir.mkdir(parents=True, exist_ok=True)
        except OSError:
            logger.warning("[sing] 下载目录不可用，退回系统临时目录")
            self._workdir = Path(tempfile.gettempdir()) / PLUGIN_NAME
            self._workdir.mkdir(parents=True, exist_ok=True)
        # 同一会话同时只跑一首，避免抢显存
        self._locks: dict[str, asyncio.Lock] = {}
        self._tasks: set[asyncio.Task] = set()
        # 待选歌单：umo -> {"songs": [...], "count": n, "ts": float}
        # 不用 SessionWaiter 了：它要求把 filter 手动塞进全局 FILTERS，
        # 插件一重载那个全局表就失效，消息会漏给大模型。
        # 改成「记下待选 + 一个纯数字监听器」，重启也不丢逻辑。
        self._pending: dict[str, dict] = {}

    # ------------------------------------------------------------ 配置

    def _cfg(self, key: str, default=None):
        value = self.config.get(key, default)
        return default if value is None else value

    def _rvc(self) -> str:
        url = str(self._cfg("rvc_url", "http://127.0.0.1:7868")).strip().rstrip("/")
        if url.endswith("/api"):
            url = url[: -len("/api")]
        return url

    # --------------------------------------------------- 统一音色（跨插件共用）

    def _shared_voice_file(self) -> Path | None:
        """两个插件共用的音色设置：data/config/voice_shared.json。

        说话和唱歌要是各用各的音色，听起来就是两个人。所以不搞两套，
        统一一份 json，两个插件都读它。
        """
        try:
            from astrbot.core.utils.astrbot_path import get_astrbot_config_path

            return Path(get_astrbot_config_path()) / SHARED_VOICE_FILE
        except Exception:  # noqa: BLE001
            return None

    def _read_shared_voice(self) -> tuple[str, float]:
        """返回 (统一音色, 文件 mtime)，没有就返回 ("", 0)。"""
        path = self._shared_voice_file()
        if not path or not path.is_file():
            return "", 0.0
        try:
            data = json.loads(path.read_text(encoding="utf-8-sig"))
            return str(data.get("voice_id") or "").strip(), path.stat().st_mtime
        except (OSError, ValueError):
            return "", 0.0

    def _write_shared_voice(self, voice_id: str) -> None:
        path = self._shared_voice_file()
        if not path or not voice_id:
            return
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            tmp = path.with_suffix(".tmp")
            tmp.write_text(
                json.dumps({"voice_id": voice_id}, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
            os.replace(tmp, path)
        except OSError:
            logger.debug("[sing] 写统一音色失败")

    def _own_config_file(self) -> Path | None:
        shared = self._shared_voice_file()
        if not shared:
            return None
        return shared.parent / (PLUGIN_NAME + "_config.json")

    def _effective_voice(self) -> str:
        """这次到底用哪个音色。

        本插件配置和统一文件一致就直接用；不一致时比 mtime —— 面板上刚保存
        的那边赢，并把结果写回统一文件，另一个插件下次读到的就是同一个。
        """
        own = str(self._cfg("voice_id", "") or "").strip()
        shared, shared_mt = self._read_shared_voice()
        if not shared:
            if own:
                self._write_shared_voice(own)
            return own
        if not own or own == shared:
            return shared
        cfg = self._own_config_file()
        try:
            own_mt = cfg.stat().st_mtime if cfg and cfg.is_file() else 0.0
        except OSError:
            own_mt = 0.0
        if own_mt > shared_mt:
            self._write_shared_voice(own)
            return own
        return shared

    def _refresh_schema_options(self, voices: list[str]) -> None:
        """把实时音色列表写回 _conf_schema.json，面板上就是下拉框了。

        AstrBot 的 schema 是加载时从磁盘读的，所以这次写进去的要下次重载才
        看得到。导入新音色后，在面板里保存一次配置或点重载，列表就更新。
        """
        if not voices:
            return
        path = Path(__file__).parent / "_conf_schema.json"
        if not path.is_file():
            return
        try:
            schema = json.loads(path.read_text(encoding="utf-8-sig"))
            field = schema.get("voice_id")
            if not isinstance(field, dict):
                return
            if field.get("options") == voices:
                return
            field["options"] = voices
            if str(field.get("default") or "").strip() not in voices:
                field["default"] = voices[0]
            path.write_text(
                json.dumps(schema, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )
            logger.info("[sing] 音色下拉列表已更新：%s", ", ".join(voices))
        except (OSError, ValueError) as exc:
            logger.debug("[sing] 更新音色列表失败：%s", exc)

    async def initialize(self) -> None:
        """插件加载后：刷新音色下拉 + 对齐说话/唱歌的音色。"""
        try:
            voices = await self._voice_ids()
        except Exception as exc:  # noqa: BLE001
            voices = []
            logger.debug("[sing] 读取音色列表失败：%s", exc)
        self._refresh_schema_options(list(voices))
        voice = self._effective_voice()
        if voice:
            logger.info("[sing] 统一音色：%s", voice)

    def _lock_for(self, umo: str) -> asyncio.Lock:
        return self._locks.setdefault(umo, asyncio.Lock())

    # ------------------------------------------------------------ HTTP

    async def _json(self, method: str, url: str, *, timeout: float = 30, **kwargs):
        """发请求并解析 JSON。连不上/超时一律返回 None，不往上抛。

        调用方要靠 None 判断失败：语音服务没起是常态，不该让异常冒到聊天里。
        """
        status = 0
        try:
            async with aiohttp.ClientSession(
                timeout=aiohttp.ClientTimeout(total=timeout),
                headers={"User-Agent": BROWSER_UA},
            ) as session:
                async with session.request(method, url, **kwargs) as resp:
                    status = resp.status
                    text = await resp.text()
        except Exception as exc:  # noqa: BLE001
            logger.debug("[sing] 请求失败 %s：%s", url, exc)
            return None
        try:
            return json.loads(text)
        except ValueError:
            return {"_status": status, "_text": text[:300]}

    # ------------------------------------------------------------ 搜歌

    async def _search_gequhai(self, keyword: str) -> list[dict]:
        try:
            async with aiohttp.ClientSession(
                timeout=aiohttp.ClientTimeout(total=25),
                headers={"User-Agent": BROWSER_UA},
            ) as session:
                # 先拿 cookie，否则 /api/music 会 403
                await session.get(GEQUHAI)
                async with session.get(
                    f"{GEQUHAI}/search", params={"s": keyword}
                ) as resp:
                    html = await resp.text()
        except Exception as exc:  # noqa: BLE001
            logger.warning("[sing] 歌曲海搜索失败：%s", exc)
            return []

        songs, seen = [], set()
        for pid, name, artist in _SEARCH_ROW.findall(html):
            if pid in seen:
                continue
            seen.add(pid)
            songs.append(
                {
                    "id": pid,
                    # 网页里的歌手名是 HTML 转义过的（HOYO-MiX&amp;當山みれい），
                    # 不还原的话会写进文件名、也会让「歌手名匹配」永远对不上
                    "name": html_lib.unescape(name.strip()),
                    "artist": html_lib.unescape(artist.strip()) or "未知",
                    "source": "gequhai",
                }
            )
        return songs

    async def _search_netease(self, keyword: str) -> list[dict]:
        data = await self._json(
            "GET",
            GDSTUDIO,
            params={
                "types": "search",
                "source": "netease",
                "name": keyword,
                "count": 20,
            },
        )
        if not isinstance(data, list):
            return []
        return [
            {
                "id": str(item.get("id")),
                "name": item.get("name") or "",
                "artist": "、".join(item.get("artist") or []) or "未知",
                "source": "netease",
            }
            for item in data
        ]

    async def _search(self, keyword: str) -> list[dict]:
        songs = await self._search_gequhai(keyword)
        if songs:
            return songs
        logger.info("[sing] 歌曲海无结果，切网易云")
        return await self._search_netease(keyword)

    # ------------------------------------------------------------ 取直链

    async def _url_gequhai(self, play_id: str) -> str:
        try:
            async with aiohttp.ClientSession(
                timeout=aiohttp.ClientTimeout(total=25),
                headers={"User-Agent": BROWSER_UA},
            ) as session:
                await session.get(GEQUHAI)
                async with session.get(f"{GEQUHAI}/play/{play_id}") as resp:
                    html = await resp.text()
                token = re.search(r"play_id = '([^']+)'", html)
                mtype = re.search(r"mp3_type = (\d+)", html)
                if not token or not mtype:
                    return ""
                async with session.post(
                    f"{GEQUHAI}/api/music",
                    data={"id": token.group(1), "type": mtype.group(1)},
                    headers={
                        "X-Requested-With": "http",
                        "X-Custom-Header": "Key",
                        "Referer": f"{GEQUHAI}/play/{play_id}",
                        "Origin": GEQUHAI,
                    },
                ) as resp:
                    payload = await resp.json()
                return ((payload.get("data") or {}).get("url") or "").strip()
        except Exception as exc:  # noqa: BLE001
            logger.warning("[sing] 歌曲海取址失败：%s", exc)
            return ""

    async def _url_netease(self, song_id: str) -> str:
        data = await self._json(
            "GET",
            GDSTUDIO,
            params={"types": "url", "source": "netease", "id": song_id, "br": "320"},
        )
        return ((data or {}).get("url") or "").strip()

    async def _resolve(self, song: dict) -> str:
        if song.get("source") == "gequhai":
            return await self._url_gequhai(song["id"]) or await self._url_netease(
                song["id"]
            )
        return await self._url_netease(song["id"]) or await self._url_gequhai(
            song["id"]
        )

    async def _download(self, url: str, dest: Path) -> int:
        try:
            async with aiohttp.ClientSession(
                timeout=aiohttp.ClientTimeout(total=300),
                headers={"User-Agent": BROWSER_UA},
            ) as session:
                async with session.get(url) as resp:
                    if resp.status != 200:
                        return 0
                    size = 0
                    with open(dest, "wb") as fh:
                        async for chunk in resp.content.iter_chunked(1 << 16):
                            fh.write(chunk)
                            size += len(chunk)
            if size < 100_000:
                dest.unlink(missing_ok=True)
                return 0
            return size
        except Exception as exc:  # noqa: BLE001
            logger.warning("[sing] 下载失败：%s", exc)
            return 0

    async def _fetch_song(self, song: dict) -> Path | None:
        # id 为空说明这个 song 是「缓存命中」造出来的占位对象，结果缓存又没
        # 用上（文件被删/改名了）。拿空 id 去取直链必然全空，重试三次也是
        # 白跑，最后报一句「没下载下来」——把责任推给网络。这里重搜一次补上 id。
        if not str(song.get("id") or "").strip():
            keyword = " ".join(
                x for x in (song.get("name") or "", song.get("artist") or "") if x
            )
            found = await self._search(keyword) if keyword else []
            good = [
                x
                for x in found
                if (x.get("name") or "").strip() == (song.get("name") or "").strip()
                and (song.get("artist") or "") in (x.get("artist") or "")
            ] or found
            if not good:
                logger.warning("[sing] 缓存占位没有 id，重搜也没结果：%s", keyword)
                return None
            song = {**good[0], "_fresh": True}
            logger.info(
                "[sing] 缓存占位补到 id=%s（%s — %s）",
                song.get("id"),
                song.get("name"),
                song.get("artist"),
            )

        safe = re.sub(r'[\\/:*?"<>|]', "_", f"{song['name']}-{song['artist']}")[:70]
        dest = self._workdir / f"{safe}.mp3"
        if dest.exists() and dest.stat().st_size > 100_000:
            return dest
        for attempt in range(3):
            url = await self._resolve(song)
            if not url:
                await asyncio.sleep(3)
                continue
            size = await self._download(url, dest)
            if size:
                logger.info("[sing] 下载完成 %.1f MB", size / 1048576)
                limit = float(self._cfg("max_seconds", 300) or 0)
                if limit > 0:
                    dur = await self._duration(dest)
                    if dur > limit:
                        logger.warning(
                            "[sing] 《%s》%.0f 秒超过上限 %.0f 秒，拒绝处理",
                            song.get("name"),
                            dur,
                            limit,
                        )
                        song["_too_long"] = f"{dur:.0f}"
                        return None
                return dest
            await asyncio.sleep(3)
        return None

    # ------------------------------------------------------------ rvc-next

    async def _health(self) -> dict | None:
        """rvc-next 的健康检查。

        它两种返回都用过：{"status": "ok"} 和 {"ok": true}，所以统一成 ok 字段。
        """
        data = await self._json("GET", f"{self._rvc()}/api/v1/app/health", timeout=8)
        if not isinstance(data, dict) or not data:
            return None
        healthy = bool(data.get("ok")) or str(data.get("status", "")).lower() == "ok"
        return {"ok": healthy, "raw": data}

    async def _upload(self, path: Path) -> str | None:
        try:
            async with aiohttp.ClientSession(
                timeout=aiohttp.ClientTimeout(total=300)
            ) as session:
                async with session.put(
                    f"{self._rvc()}/api/v1/audio/uploads",
                    params={"name": path.name},
                    data=path.read_bytes(),
                    headers={"Content-Type": "application/octet-stream"},
                ) as resp:
                    info = await resp.json()
            return info.get("path")
        except Exception as exc:  # noqa: BLE001
            logger.warning("[sing] 上传失败：%s", exc)
            return None

    async def _submit(self, server_path: str, preset: str) -> dict:
        payload = {
            "inputs": [{"kind": "path", "path": server_path}],
            "voice_id": self._effective_voice() or "xilian",
            "separate": {"preset": preset},
            "remix": {"gain_db": 0.0, "vocal_gain_db": 0.0},
            "output_format": "mp3",
        }
        # 唱歌的音色参数单独给，不跟说话那边共用一个值。
        # 以前这里只传 pitch，index_rate/protect 一个都没传，rvc-next 就拿它
        # 自己的默认值 0.75/0.33 跑了——看着像"特意配好的"，其实没人配过。
        # 说话那边用的是 0.55/0.45（桥接 service/.env）：
        #   说话要字清楚，protect 高一点保住气声和辅音；
        #   唱歌本来就有旋律和延音，气声靠唱腔，反而应该更贴模型音色。
        params: dict[str, float] = {}
        pitch = float(self._cfg("pitch", 0.0))
        if pitch:
            params["pitch"] = pitch
        index_rate = self._cfg("index_rate", None)
        if index_rate is not None:
            params["index_rate"] = max(0.0, min(1.0, float(index_rate)))
        protect = self._cfg("protect", None)
        if protect is not None:
            params["protect"] = max(0.0, min(0.5, float(protect)))
        f0_method = str(self._cfg("f0_method", "") or "").strip()
        if f0_method:
            params["f0_method"] = f0_method
        if params:
            payload["params"] = params
        return await self._json(
            "POST", f"{self._rvc()}/api/v1/convert", json=payload, timeout=120
        )

    async def _wait(self, job_id: str) -> dict:
        deadline = time.monotonic() + float(self._cfg("timeout", 900))
        while time.monotonic() < deadline:
            job = await self._json(
                "GET", f"{self._rvc()}/api/v1/jobs/{job_id}", timeout=20
            )
            if not isinstance(job, dict):
                await asyncio.sleep(4)
                continue
            if job.get("state") in ("completed", "failed", "cancelled"):
                return job
            await asyncio.sleep(4)
        return {"state": "timeout"}

    @staticmethod
    def _is_oom(job: dict) -> bool:
        err = str(job.get("error") or "").lower()
        return "out of memory" in err or "cuda" in err

    async def _convert(self, audio: Path, song_label: str = "") -> Path | None:
        server_path = await self._upload(audio)
        if not server_path:
            return None

        base = str(self._cfg("preset", "karaoke"))
        chain = [base] + [p for p in PRESET_FALLBACK if p != base]
        for idx, preset in enumerate(chain):
            job = await self._submit(server_path, preset)
            job_id = job.get("id")
            if not job_id:
                logger.warning("[sing] 提交失败：%s", str(job)[:200])
                return None
            result = await self._wait(job_id)
            if result.get("state") == "completed":
                outputs = (result.get("result") or {}).get("outputs") or []
                if outputs:
                    out = Path(outputs[0])
                    if out.exists():
                        return self._save_output(out, song_label)
                return None
            if self._is_oom(result) and idx + 1 < len(chain):
                logger.info("[sing] 显存不够，换 %s 重试", chain[idx + 1])
                await self._json(
                    "POST", f"{self._rvc()}/api/v1/compute/release", json={}, timeout=20
                )
                await asyncio.sleep(5)
                continue
            logger.warning("[sing] 转换失败：%s", str(result.get("error"))[:200])
            return None
        return None

    # ------------------------------------------------------------ 后台任务

    @staticmethod
    async def _duration(path: Path) -> float:
        """读音频时长（秒）。读不到返回 0。"""
        try:
            proc = await asyncio.create_subprocess_exec(
                "ffprobe", "-v", "quiet",
                "-show_entries", "format=duration",
                "-of", "csv=p=0", str(path),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.DEVNULL,
            )
            out, _ = await proc.communicate()
            return float(out.decode("utf-8", "ignore").strip() or 0)
        except (OSError, ValueError):
            return 0.0

    def _voice_dir(self) -> Path | None:
        """当前音色专属的成品目录：output_sing/<音色id>/。

        成品必须按音色分开存。以前所有音色的歌都堆在 output_sing 根目录，
        缓存只按「歌名-歌手」匹配，根本不看是哪副嗓子唱的 —— 换个音色再点
        同一首歌，发出去的还是旧音色那一版，听着像"换了音色没生效"。
        分开之后，每个音色只认自己目录里的成品，不会再串。
        """
        if not self._outdir:
            return None
        voice = re.sub(r'[\\/:*?"<>|]', "_", (self._effective_voice() or "default"))[:40]
        d = self._outdir / voice
        try:
            d.mkdir(parents=True, exist_ok=True)
            return d
        except OSError:
            logger.warning("[sing] 音色目录不可用，退回成品根目录")
            return self._outdir

    def _find_cached_by_name(self, name: str) -> tuple[Path, str, str] | None:
        """只按歌名找缓存，不限歌手（但只在当前音色的目录里找）。

        返回 (路径, 歌名, 歌手)。成品命名是「歌名-歌手_时间.mp3」，
        所以按「歌名-」前缀匹配，从文件名反推歌手。
        """
        vdir = self._voice_dir()
        if not vdir or not vdir.is_dir():
            return None
        safe = re.sub(r'[\\/:*?"<>|]', "_", name)[:70]
        hits: list[tuple[float, Path, str]] = []
        try:
            for p in vdir.iterdir():
                if not p.is_file() or p.suffix.lower() not in (".mp3", ".wav"):
                    continue
                if p.stat().st_size < 100_000:
                    continue
                stem = p.name[: -len(p.suffix)]
                # 去掉末尾的 _月日-时分 或 _月日-时分_1
                base = re.sub(r"_\d{4}-\d{4}(_\d+)?$", "", stem)
                if not base.startswith(f"{safe}-"):
                    continue
                found_artist = base[len(safe) + 1 :]
                hits.append((p.stat().st_mtime, p, found_artist))
        except OSError:
            return None
        if not hits:
            return None
        _, path, artist = max(hits, key=lambda x: x[0])
        return path, name, artist

    def _find_cached(self, name: str, artist: str) -> Path | None:
        """在**当前音色**的成品目录里找这首歌，找到就复用。

        成品命名是「歌名-歌手_月日-时分.mp3」，所以按「歌名-歌手_」前缀匹配。
        取最新的一版。只看本音色目录，别音色的同名成品一律不算命中。
        """
        vdir = self._voice_dir()
        if not vdir or not vdir.is_dir():
            return None
        safe = re.sub(r'[\\/:*?"<>|]', "_", f"{name}-{artist}")[:70]
        try:
            hits = [
                p
                for p in vdir.iterdir()
                if p.is_file()
                and p.suffix.lower() in (".mp3", ".wav")
                and p.stat().st_size > 100_000
                # 早期成品是「歌名-歌手.mp3」不带时间戳。只认 f"{safe}_" 的话
                # 这类一个都匹配不上，明明唱过还要重下一遍，下载一失败就报
                # 「没下载下来」——看着像网络问题，其实是缓存没被认出来。
                and (p.name.startswith(f"{safe}_") or p.stem == safe)
            ]
        except OSError:
            return None
        if not hits:
            return None
        return max(hits, key=lambda p: p.stat().st_mtime)

    def _save_output(self, src: Path, label: str) -> Path:
        """把 rvc 的成品复制一份到当前音色的目录，按歌名-日期命名。"""
        vdir = self._voice_dir()
        if not vdir:
            return src
        try:
            safe = re.sub(r'[\\/:*?"<>|]', "_", label or src.stem)[:70]
            stamp = time.strftime("%m%d-%H%M")
            dst = vdir / f"{safe}_{stamp}{src.suffix}"
            n = 1
            while dst.exists():
                dst = vdir / f"{safe}_{stamp}_{n}{src.suffix}"
                n += 1
            shutil.copy2(src, dst)
            logger.info("[sing] 成品已保存 %s/%s", vdir.name, dst.name)
            return dst
        except Exception as exc:  # noqa: BLE001
            logger.warning("[sing] 保存成品失败：%s", exc)
            return src

    def _spawn(self, coro) -> None:
        task = asyncio.create_task(coro)
        self._tasks.add(task)
        task.add_done_callback(self._tasks.discard)

    async def _send_audio(self, umo: str, src: Path, caption: str = "") -> bool:
        """直接发 mp3 原始字节，不重编码。

        Record.convert_to_base64() 写死 target_format="wav"，会把 mp3 转成
        48kHz 立体声，一首 4 分半的歌 base64 后 68MB，QQ 发不出去。
        但 MediaResolver 本身支持 preserve_mp3=True（实测 4.26MB mp3 ->
        5.68MB base64，零音质损失）。这里绕开 Record，自己拼 onebot 消息段。
        """
        try:
            b64 = await MediaResolver(
                str(src), media_type="audio", default_suffix=".mp3"
            ).to_base64(preserve_mp3=True)
        except Exception:  # noqa: BLE001
            logger.exception("[sing] 读取音频失败，回退 Record")
            b64 = None

        platform = None
        try:
            for pf in self.context.platform_manager.platform_insts:
                if pf.meta().id == MessageSesion.from_str(umo).platform_name:
                    platform = pf
                    break
        except Exception:  # noqa: BLE001
            platform = None

        if b64 and platform is not None and hasattr(platform, "bot"):
            try:
                session = MessageSesion.from_str(umo)
                is_group = session.message_type == MessageType.GROUP_MESSAGE
                sid = (
                    session.session_id.split("_")[-1]
                    if is_group
                    else session.session_id
                )
                segments = []
                if caption:
                    segments.append({"type": "text", "data": {"text": caption}})
                segments.append(
                    {"type": "record", "data": {"file": f"base64://{b64}"}}
                )
                act = "send_group_msg" if is_group else "send_private_msg"
                key = "group_id" if is_group else "user_id"
                await platform.bot.call_action(
                    act, **{key: int(sid)}, message=segments
                )
                logger.info(
                    "[sing] 已发送 %s（mp3 直传 %.1f MB）",
                    src.name,
                    len(b64) / 1048576,
                )
                return True
            except Exception:  # noqa: BLE001
                logger.exception("[sing] 直传失败，回退 Record")

        # 回退：交给 AstrBot 正常链路
        chain = []
        if caption:
            chain.append(Plain(caption))
        chain.append(Record(file=str(src), path=str(src)))
        await self.context.send_message(umo, MessageChain(chain))
        return True

    async def _her_words(
        self,
        umo: str,
        song: dict,
        *,
        cached: bool = False,
    ) -> str | None:
        """让模型用她自己的口吻说一句话，附在歌前面发出去。

        这样她"知道"自己刚唱完——这句话是她自己生成的，同时也会进入她的
        会话上下文，下一轮她就记得"我刚给他唱了一首"。
        失败就返回 None，退回固定文案，不影响发送。
        """
        name = song.get("name") or ""
        artist = song.get("artist") or ""
        if cached:
            fact = (
                f"你刚把之前唱过的《{name}》（{artist}）发给对方了，"
                "音频已经发出去，对方能听到。"
            )
        else:
            fact = (
                f"你刚唱完《{name}》（{artist}），音频已经发到对方那里，对方能听到。"
                "这是真的唱完了，不是许诺。"
            )
        prompt = (
            fact
            + "\n\n现在用你自己的口吻说**一句话**告诉对方，就像刚唱完喘口气那样。"
            "要求：不要播报歌名和歌手、不要用「为你献上」「希望你喜欢」这种话、"
            "不要加引号、不要问对方要不要再唱、不超过 30 字。"
            "只输出这句话本身。"
        )
        try:
            prov = await self.context.get_using_provider_async(umo=str(umo))
            if prov is None:
                return None
            provider_id = (
                getattr(prov, "provider_config", {}).get("id")
                or getattr(prov, "provider_id", None)
            )
            if not provider_id:
                return None

            resp = await self.context.tool_loop_agent(
                event=None,
                chat_provider_id=provider_id,
                prompt=prompt,
                contexts=[],
                max_steps=1,
            )
            text = (getattr(resp, "completion_text", "") or "").strip()
            text = text.strip("“”\"'「」 \n")
            if not text:
                return None
            # 太长的截断，避免她一口气说一堆
            if len(text) > 60:
                text = text[:60].rstrip("，,。. ") + "…"
            logger.info("[sing] 她自己的话：%s", text)
            await self._remember_performance(umo, song, text, cached=cached)
            return text
        except Exception as exc:  # noqa: BLE001
            logger.warning("[sing] 生成她的话失败，用固定文案：%s", exc)
            return None

    async def _remember_performance(
        self,
        umo: str,
        song: dict,
        said: str,
        *,
        cached: bool = False,
    ) -> None:
        """把「刚唱完这首歌」记进她的会话，下一轮她才记得。

        AstrBot 只让插件以 user 角色追加消息，所以写成一条像样的记录，
        让她读起来就是"刚发生的事"，不像别人在跟她说话。
        """
        if not self._cfg("remember_singing", True):
            return
        try:
            mgr = getattr(self.context, "conversation_manager", None)
            if mgr is None:
                return
            cid = await mgr.get_curr_conversation_id(umo)
            if not cid:
                return
            name = song.get("name") or ""
            artist = song.get("artist") or ""
            verb = "重发了一遍之前唱的" if cached else "刚唱完"
            record = (
                f"[歌] 我{verb}《{name}》（{artist}），已经用语音发过去了，"
                f"对方能听到。我当时说的是：「{said}」"
            )
            await mgr.append_message(record, cid=cid)
            logger.info("[sing] 已记进会话 %s", cid[:8])
        except Exception as exc:  # noqa: BLE001
            logger.debug("[sing] 记录唱歌失败（不影响发送）：%s", exc)

    async def _run_sing(self, event: AstrMessageEvent, song: dict) -> None:
        """后台跑完一首歌，然后把语音主动发出去。"""
        umo = event.unified_msg_origin
        label = f"{song['name']} — {song['artist']}"
        async with self._lock_for(umo):
            try:
                # 唱过就直接发，不再下载 + 转换一遍
                if self._cfg("reuse_cache", True) and not song.get("_fresh"):
                    cached = self._find_cached(song["name"], song["artist"])
                    if cached:
                        logger.info("[sing] 命中缓存 %s，跳过转换", cached.name)
                        caption = (
                            await self._her_words(umo, song, cached=True)
                            if self._cfg("send_text", True)
                            else ""
                        ) or ""
                        await self._send_audio(umo, cached, caption)
                        return

                audio = await self._fetch_song(song)
                if not audio:
                    if song.get("_too_long"):
                        await self.context.send_message(
                            umo,
                            MessageChain(
                                [
                                    Plain(
                                        f"《{label}》有 {song['_too_long']} 秒，"
                                        f"超过了 {self._cfg('max_seconds', 300)} 秒上限。"
                                        "要么换个短一点的版本，要么改高上限。"
                                    )
                                ]
                            ),
                        )
                        return
                    await self.context.send_message(
                        umo, MessageChain([Plain(f"《{label}》没下载下来，换个版本试试～")])
                    )
                    return
                out = await self._convert(audio, f"{song['name']}-{song['artist']}")
                if not out:
                    await self.context.send_message(
                        umo,
                        MessageChain([Plain(f"《{label}》没唱成，可能是显存不够或者服务没起。")]),
                    )
                    return

                caption = (
                    await self._her_words(umo, song)
                    if self._cfg("send_text", True)
                    else ""
                ) or ""
                await self._send_audio(umo, out, caption)
            except asyncio.CancelledError:
                raise
            except Exception:  # noqa: BLE001
                logger.exception("[sing] 唱歌任务异常")
                try:
                    await self.context.send_message(
                        umo, MessageChain([Plain("唱歌的时候出错了，看一眼日志。")])
                    )
                except Exception:  # noqa: BLE001
                    pass

    def _allowed(self, event: AstrMessageEvent) -> bool:
        """私聊随时能用；群里看配置，关着时只有管理员。"""
        if self._cfg("group_on", False):
            return True
        if event.get_message_type() == MessageType.FRIEND_MESSAGE:
            return True
        return event.is_admin()

    # ------------------------------------------------------------ 指令

    @filter.command("唱歌")
    async def sing(self, event: AstrMessageEvent):
        """让她唱一首歌：/唱歌 心湖 或 /唱歌 心湖 张靓颖"""
        if not self._cfg("enabled", True):
            yield event.plain_result("唱歌功能关着。")
            return
        if not self._allowed(event):
            yield event.plain_result("群里点歌得找管理员开，或者私聊我唱～")
            return

        raw = (event.message_str or "").strip()
        parts = raw.split(maxsplit=1)
        keyword = parts[1].strip() if len(parts) > 1 else ""
        # 强制重新转换、不吃缓存。「重唱」两个字单独打就行，-- 可有可无
        # 按长度从长到短匹配，免得「--重唱」被「重唱」先剥掉一半留下个 --；
        # 剥完必须还剩东西，否则 /唱歌 重唱 这种歌名恰好叫「重唱」会被吃空。
        fresh = False
        for flag in ("--fresh", "--重唱", "重唱一遍", "重唱", "-f"):
            if keyword.endswith(flag) and keyword[: -len(flag)].strip():
                fresh = True
                keyword = keyword[: -len(flag)].strip()
                break
        if not keyword:
            yield event.plain_result(HELP_TEXT)
            return

        health = await self._health()
        if not health or not health.get("ok"):
            yield event.plain_result(
                "唱不了：rvc-next 没连上或者 RVC 异常。\n"
                f"地址：{self._rvc()}"
            )
            return

        songs = await self._search(keyword)
        if not songs:
            yield event.plain_result(f"搜不到《{keyword}》，换个名字试试。")
            return

        for s_ in songs:
            s_["_fresh"] = fresh

        # 关键词里带了歌手名就自动筛：/唱歌 心湖 张靓颖
        picked = self._match_by_artist(keyword, songs)

        # 只剩一个就没什么好选的，直接唱
        if picked is not None:
            yield event.plain_result(f"开唱：{picked['name']} — {picked['artist']}")
            self._spawn(self._run_sing(event, picked))
            return

        if len(songs) == 1:
            song = songs[0]
            yield event.plain_result(f"开唱：{song['name']} — {song['artist']}")
            self._spawn(self._run_sing(event, song))
            return

        yield event.plain_result(self._candidate_text(keyword, songs))
        # 记下候选，等用户回数字；选了由 _pick_listener 接手开唱
        self._ask_pick(event, songs)

    def _match_by_artist(self, keyword: str, songs: list[dict]) -> dict | None:
        """关键词末尾如果是某位歌手，就返回那位歌手的那首。"""
        words = keyword.split()
        if len(words) < 2:
            return None
        # 依次尝试末尾 1~2 个词当歌手名
        for span in (2, 1):
            if len(words) <= span:
                continue
            artist_hint = " ".join(words[-span:])
            hits = [s for s in songs if artist_hint in s["artist"]]
            if len(hits) == 1:
                return hits[0]
        return None

    def _pick_best(
        self,
        keyword: str,
        songs: list[dict],
        artist_hint: str = "",
    ) -> dict:
        """从搜索结果里挑最该唱的那版。

        优先级：
          1. 有成品缓存（只按歌名，不看歌手）→ 用回那版，直接秒发
          2. 指定了歌手 / 关键词里带歌手 → 那位
          3. 歌名和关键词完全一致
          4. 歌名包含关键词
          5. 兜底挑最短的
        全程排除伴奏、纯音乐、卡拉OK版（除非只剩这些）。
        """
        bad = ("伴奏", "纯音乐", "卡拉OK", "karaoke", "instrumental", "off vocal")
        good = [x for x in songs if not any(b in (x.get("name") or "") for b in bad)]
        pool = good or songs

        # 1) 缓存优先（名字对上就行，歌手不管）
        #    注意：这里原本只取第一个词去匹配，中文歌名没事（「心湖 张靓颖」取「心湖」），
        #    但英文歌名一有空格就必然漏 ——「Yesterday Once More」取成「Yesterday」，
        #    永远对不上「Yesterday Once More-Carpenters_xxx.mp3」，每次都白重唱一遍。
        #    所以带空格时整串先试，再退回首词（首词那条是为「歌名 歌手」的写法留的）。
        if self._cfg("reuse_cache", True):
            cached = None
            for probe in (keyword, keyword.split()[0] if keyword.split() else keyword):
                cached = self._find_cached_by_name(probe)
                if cached:
                    break
            if cached:
                _, cname, cartist = cached
                # 把它变成一个 song 对象，标记命中
                for x in pool:
                    if (x.get("name") or "").strip() == cname and (
                        cartist in (x.get("artist") or "")
                        or (x.get("artist") or "") in cartist
                    ):
                        x = dict(x)
                        x["name"], x["artist"] = cname, cartist
                        return x
                # 搜索结果里没有这一版也照样用缓存
                return {
                    "id": "",
                    "name": cname,
                    "artist": cartist,
                    "source": "cache",
                }

        # 2) 歌手
        if artist_hint:
            hits = [x for x in pool if artist_hint in (x.get("artist") or "")]
            if hits:
                return hits[0]
        m = self._match_by_artist(keyword, pool)
        if m is not None:
            return m

        # 3) 歌名完全一致
        base = keyword.split()[0] if keyword.split() else keyword
        exact = [x for x in pool if (x.get("name") or "").strip() == base]
        if exact:
            return exact[0]

        # 4) 包含
        contains = [x for x in pool if base in (x.get("name") or "")]
        if contains:
            return contains[0]

        # 5) 兜底
        return sorted(pool, key=lambda x: len(x.get("name") or ""))[0]

    def _candidate_text(self, keyword: str, songs: list[dict]) -> str:
        count = min(int(self._cfg("list_count", 8)), len(songs))
        lines = [f"《{keyword}》找到 {len(songs)} 个版本，要唱哪个？"]
        for i in range(count):
            song = songs[i]
            lines.append(f"{i + 1}. {song['name']} — {song['artist']}")
        if len(songs) > count:
            lines.append(f"（只列前 {count} 个）")
        lines.append("回一个数字，或者回「取消」。")
        return "\n".join(lines)

    def _ask_pick(self, event: AstrMessageEvent, songs: list[dict]) -> None:
        """把候选记下来，等用户回数字。由下面的 _pick_listener 接手。"""
        count = min(int(self._cfg("list_count", 8)), len(songs))
        self._pending[event.unified_msg_origin] = {
            "songs": songs[:count],
            "count": count,
            "ts": time.time(),
            "umo": event.unified_msg_origin,
        }

    # 聊天里点名要听歌（模型没调工具时的兜底）
    _SING_TRIGGER = (
        r"(?:想听你唱|想听|要听|听你唱|唱给我听|唱给我|唱首|"
        r"来一首|来首|唱个|唱一下|给我唱|你会唱)"
    )
    _SING_TAIL = re.compile(
        r"(吧|呀|啊|哦|嘛|呗|好不好|可以吗|行吗|给我听|给我|行不行|吗|呢|了)$"
    )
    _SING_LEAD = re.compile(r"^(你唱|你|唱|首|个|一首|一首歌|歌|的|给|我|来|再)+")
    _SING_JUNK = {"歌", "首歌", "什么", "说说话", "说话", "听", "唱"}

    @filter.regex(
        r"(?:想听|要听|听你唱|唱给我|唱首|来一首|来首|唱个|唱一下|给我唱|你会唱)"
        r"[《「\"']?[\u4e00-\u9fa5A-Za-z0-9 ()（）·\-]{1,30}"
    )
    async def _chat_sing_listener(self, event: AstrMessageEvent):
        """模型没调工具时的兜底：从聊天里认出「想听你唱XX」。

        正常情况应该由 sing_song 工具处理，这里只在模型没动静时补位。
        宁可漏掉，也不要误判——误判会打断正常聊天。
        """
        if not self._cfg("enabled", True) or not self._cfg("chat_trigger", True):
            return
        if event.get_extra("sing_handled"):
            return

        name = self._extract_song_name(event.message_str or "")
        if not name:
            return

        health = await self._health()
        if not health or not health.get("ok"):
            return

        songs = await self._search(name)
        if not songs:
            return
        picked = self._pick_best(name, songs)
        picked["_fresh"] = False

        event.set_extra("sing_handled", True)
        event.stop_event()
        cached = self._find_cached(picked["name"], picked["artist"])
        self._spawn(self._run_sing(event, picked))
        if cached:
            yield event.plain_result(f"《{picked['name']}》这首之前唱过，马上给你。")
        else:
            yield event.plain_result(
                f"好，给你唱《{picked['name']}》——{picked['artist']}，等我一会儿。"
            )

    def _extract_song_name(self, text: str) -> str | None:
        """从一句话里抠出歌名，抠不准就返回 None。"""
        # ① 书名号/引号最可靠
        m = re.search(r"[《「“\"']([^》」”\"']{1,30})[》」”\"']", text)
        if m:
            got = m.group(1).strip()
            if got and got not in self._SING_JUNK:
                return got

        # ② 触发词后面那段
        m = re.search(self._SING_TRIGGER + r"\s*(.{1,30})", text)
        if not m:
            return None
        name = m.group(1).strip()
        for _ in range(3):
            name = self._SING_TAIL.sub("", name).strip()
            name = self._SING_LEAD.sub("", name).strip()
        if not name or name in self._SING_JUNK:
            return None
        # 太短、或者明显不是歌名（比如纯语气）
        if len(name) < 2:
            return None
        return name

    @filter.regex(r"^\s*(?:\d+|取消|算了|不唱了|q)\s*$")
    async def _pick_listener(self, event: AstrMessageEvent):
        """只在「整条消息就是个数字」时被激活，拦下选歌。
        没有待选歌单时什么都不做，照常当普通聊天处理。"""
        umo = event.unified_msg_origin
        pending = self._pending.get(umo)
        if not pending:
            return
        if time.time() - pending["ts"] > 90:
            self._pending.pop(umo, None)
            yield event.plain_result("等太久了，先不唱了。要唱再 /唱歌 一次。")
            event.stop_event()
            return

        text = (event.message_str or "").strip()
        if text in ("取消", "算了", "不唱了", "q"):
            self._pending.pop(umo, None)
            yield event.plain_result("好，那不唱了。")
            event.stop_event()
            return
        index = int(text) - 1
        if index < 0 or index >= pending["count"]:
            yield event.plain_result(f"只有 1~{pending['count']}，重新选一个。")
            event.stop_event()
            return

        self._pending.pop(umo, None)
        song = pending["songs"][index]
        yield event.plain_result(f"开唱：{song['name']} — {song['artist']}")
        self._spawn(self._run_sing(_EventStub(pending["umo"]), song))
        event.stop_event()

    @filter.command("发歌")
    async def resend_audio(self, event: AstrMessageEvent):
        """把当前音色目录里最新的一首用新方法发一遍（只测发送，不重新转换）。"""
        if not self._allowed(event):
            yield event.plain_result("不行～")
            return
        vdir = self._voice_dir()
        if not vdir or not vdir.is_dir():
            yield event.plain_result("成品目录还没配置。")
            return
        files = sorted(
            (p for p in vdir.iterdir() if p.suffix.lower() in (".mp3", ".wav")),
            key=lambda p: p.stat().st_mtime,
            reverse=True,
        )
        if not files:
            yield event.plain_result(f"{vdir.name} 这个音色下还没有唱过的歌。")
            return
        target = files[0]
        size = target.stat().st_size / 1048576
        yield event.plain_result(f"发这首：{target.name}（{size:.1f} MB）")
        ok = await self._send_audio(event.unified_msg_origin, target, "")
        if not ok:
            yield event.plain_result("发送失败，看日志。")

    @filter.command("点歌")
    async def order_song(self, event: AstrMessageEvent):
        """/点歌 <歌名>，和 /唱歌 一样。"""
        async for result in self.sing(event):
            yield result

    @filter.command("唱歌列表")
    async def sing_list(self, event: AstrMessageEvent):
        """只搜不唱，看看有哪些版本可选。"""
        raw = (event.message_str or "").strip()
        parts = raw.split(maxsplit=1)
        keyword = parts[1].strip() if len(parts) > 1 else ""
        if not keyword:
            yield event.plain_result("用法：/唱歌列表 <歌名>")
            return
        songs = await self._search(keyword)
        if not songs:
            yield event.plain_result(f"搜不到《{keyword}》。")
            return
        count = int(self._cfg("list_count", 8))
        lines = [f"《{keyword}》找到这些："]
        for i, song in enumerate(songs[:count]):
            lines.append(f"{i + 1}. {song['name']} — {song['artist']}")
        lines.append("用 /唱歌 歌名 直接唱；想指定版本就说清楚歌手。")
        yield event.plain_result("\n".join(lines))

    async def _voice_ids(self) -> list[str]:
        """从模型库里取音色 id 列表。"""
        data = await self._json("GET", f"{self._rvc()}/api/v1/models", timeout=15)
        if not isinstance(data, list):
            return []
        return [str(m.get("id")) for m in data if isinstance(m, dict) and m.get("id")]

    @filter.command("唱歌状态")
    async def sing_status(self, event: AstrMessageEvent):
        """看唱歌服务是否就绪。"""
        health = await self._health()
        if not health:
            yield event.plain_result(
                f"连不上 rvc-next：{self._rvc()}\n"
                "先把语音服务起来（启动语音服务.bat 或 TTS-RVC-Service）。"
            )
            return
        voices = await self._voice_ids()
        current = self._effective_voice() or "xilian"
        mark = "" if not voices or current in voices else "  ← 模型库里没有这个！"
        yield event.plain_result(
            f"rvc-next：{'正常' if health.get('ok') else '异常'}\n"
            f"可用音色：{', '.join(voices) if voices else '无'}\n"
            f"唱歌用：{current}{mark}\n"
            f"分离预设：{self._cfg('preset', 'karaoke')}\n"
            f"变调：{self._cfg('pitch', 0.0):+g} 半音"
        )

    @filter.command("唱歌帮助")
    async def sing_help(self, event: AstrMessageEvent):
        """查看唱歌指令。"""
        yield event.plain_result(HELP_TEXT)

    # ------------------------------------------------------------ LLM 工具

    @filter.llm_tool(name="sing_song")
    async def sing_song_tool(self, event: AstrMessageEvent, song: str, artist: str = ""):
        """唱一首歌给对方听（用你自己的音色，唱整首，不是念歌词）。

        什么时候用：对方用任何自然说法想听你唱——「我想听你唱心湖」
        「给我唱首虫儿飞」「你会唱XX吗」「来一首XX」「唱个歌呗」
        「上一次那首」「再来一遍」——都直接调，不要反问他具体版本。

        不要用这个工具的情况：
        - 对方只是聊到某首歌、提到歌手，不是要你唱
        - 对方是让你念歌词或朗读，不是唱
        - 你已经在唱了，别重复调

        Args:
            song(string): 歌名。只填歌名本身，不要带「我想听」「唱一首」这些话。
                可以是模糊的，搜不到会自动判断。
            artist(string): 可选，歌手名。对方明确说了歌手才填，比如「张靓颖」。
                没提就留空，会挑最热门那版。
        """
        if not self._cfg("enabled", True) or not self._cfg("llm_tool_enabled", True):
            return "唱歌功能没开。"

        health = await self._health()
        if not health or not health.get("ok"):
            return "唱不了：rvc-next 没连上。"

        keyword = " ".join(x for x in (song.strip(), artist.strip()) if x)
        songs = await self._search(keyword)
        if not songs:
            # 去掉歌手名再试一次，避免歌手名拖累搜索
            if artist:
                songs = await self._search(song.strip())
            if not songs:
                return f"搜不到《{song}》，告诉对方换个说法或者你记不清这首歌。"

        picked = self._pick_best(song.strip() or keyword, songs, artist.strip())
        picked["_fresh"] = False
        cached = self._find_cached(picked["name"], picked["artist"])
        self._spawn(self._run_sing(event, picked))

        who = picked["artist"]
        if cached:
            return (
                f"《{picked['name']}》这首之前唱过（{who}），现在直接发过来，几秒钟就好。"
                "跟对方说一句「这首我唱过，马上给你」，别说是重新录的。"
            )
        return (
            f"开始唱《{picked['name']}》了（{who}），大概一两分钟，唱完语音自动发过来。"
            "现在只跟对方说一句「在准备了，等我一下」这类自然的话，"
            "不要说歌名播报、不要重复点歌、不要再调这个工具。"
        )
