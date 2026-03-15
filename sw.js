const APP_SHELL_CACHE = "life-tracker-app-shell-v18";
const APP_SHELL_CACHE_PREFIX = "life-tracker-app-shell-";
const COMMANDER_IMAGE_CACHE = "life-tracker-commander-images-v1";
const MAX_CACHED_IMAGES = 180;

const CRITICAL_APP_SHELL_ASSETS = [
  "./",
  "./index.html",
  "./style.css",
  "./app.js",
  "./vendor/qrcode.min.js",
  "./scripts/build-static.mjs",
  "./manifest.webmanifest",
  "./icons/favicon.png",
  "./icons/app-Icon.png",
  "./icons/Back.svg",
  "./icons/Cancel.svg",
  "./icons/GameLog.svg",
  "./icons/Edit.svg",
  "./icons/delete.svg",
  "./icons/JudyArrowHead.png",
  "./icons/Minus.svg",
  "./icons/Monarch.svg",
  "./icons/Ok.svg",
  "./icons/Pause.svg",
  "./icons/Play.svg",
  "./icons/Poison.svg",
  "./icons/Plus.svg",
  "./icons/profile.svg",
  "./fonts/GoogleSansCode-Bold.woff",
  "./fonts/GoogleSansCode-BoldItalic.woff",
  "./fonts/GoogleSansCode-ExtraBold.woff",
  "./fonts/GoogleSansCode-ExtraBoldItalic.woff",
  "./fonts/GoogleSansCode-Italic.woff",
  "./fonts/GoogleSansCode-Light.woff",
  "./fonts/GoogleSansCode-LightItalic.woff",
  "./fonts/GoogleSansCode-Medium.woff",
  "./fonts/GoogleSansCode-MediumItalic.woff",
  "./fonts/GoogleSansCode-Regular.woff",
  "./fonts/GoogleSansCode-SemiBold.woff",
  "./fonts/GoogleSansCode-SemiBoldItalic.woff",
  "./img/default_back0.png",
  "./img/default_back1.png",
  "./img/menu_back.png",
  "./custom-art/custom_bello.png",
  "./custom-art/custom_krenko.png",
  "./custom-art/custom_morcant.png",
  "./custom-art/custom_nekuzar.png",
  "./custom-art/custom_prosper.png",
  "./custom-art/custom_rith.png",
  "./custom-art/custom-pako.png",
  "./icons/QR.svg",
  "./icons/buttonshape.svg"
];

const APP_SHELL_ASSETS = [
];

function getCacheKeysForUrl(input) {
  const url = new URL(typeof input === "string" ? input : input.url, self.location.origin);
  const pathname = url.pathname || "/";
  const keys = new Set([
    pathname,
    `.${pathname}`
  ]);

  if (pathname === "/" || pathname === "/index.html") {
    keys.add("./");
    keys.add("./index.html");
    keys.add("/");
    keys.add("/index.html");
  }

  return Array.from(keys);
}

async function putAppShellResponse(cache, requestOrUrl, response) {
  const safeResponse = await toCacheSafeResponse(response);
  const keys = getCacheKeysForUrl(requestOrUrl);
  await Promise.all(keys.map((key) => cache.put(key, safeResponse.clone())));
}

async function matchAppShellRequest(cache, requestOrUrl) {
  const keys = getCacheKeysForUrl(requestOrUrl);
  for (const key of keys) {
    const cached = await cache.match(key, { ignoreSearch: true });
    if (cached) return cached;
  }
  return null;
}

async function matchAppShellRequestAcrossCaches(requestOrUrl) {
  const currentCache = await caches.open(APP_SHELL_CACHE);
  const currentMatch = await matchAppShellRequest(currentCache, requestOrUrl);
  if (currentMatch) return currentMatch;

  const cacheKeys = await caches.keys();
  const legacyShellCaches = cacheKeys.filter((key) =>
    key !== APP_SHELL_CACHE && key.startsWith(APP_SHELL_CACHE_PREFIX)
  );

  for (const key of legacyShellCaches) {
    try {
      const cache = await caches.open(key);
      const match = await matchAppShellRequest(cache, requestOrUrl);
      if (match) return match;
    } catch {
      // Ignore a single cache read failure and continue.
    }
  }

  return null;
}

async function cacheAssetList(cache, assets) {
  await Promise.all(assets.map(async (asset) => {
    try {
      const response = await fetch(asset, { cache: "no-cache" });
      if (!response || !response.ok) return;
      await putAppShellResponse(cache, asset, response);
    } catch {
      // Keep installing the worker even if one asset is unavailable.
    }
  }));
}

function cloneHeaders(headers) {
  const copied = new Headers();
  headers.forEach((value, key) => {
    copied.set(key, value);
  });
  return copied;
}

async function toCacheSafeResponse(response) {
  if (!response) return response;
  if (!response.redirected) return response;

  const headers = cloneHeaders(response.headers);
  const body = await response.clone().blob();
  return new Response(body, {
    status: response.status,
    statusText: response.statusText,
    headers
  });
}

self.addEventListener("install", (event) => {
  event.waitUntil((async () => {
    const cache = await caches.open(APP_SHELL_CACHE);
    await cacheAssetList(cache, CRITICAL_APP_SHELL_ASSETS);
    await cacheAssetList(cache, APP_SHELL_ASSETS);
  })());
  self.skipWaiting();
});

self.addEventListener("activate", (event) => {
  event.waitUntil((async () => {
    const validCaches = new Set([APP_SHELL_CACHE, COMMANDER_IMAGE_CACHE]);
    const keys = await caches.keys();
    await Promise.all(keys.map((key) => {
      const isLegacyShellCache = key.startsWith(APP_SHELL_CACHE_PREFIX);
      if (!validCaches.has(key) && !isLegacyShellCache) {
        return caches.delete(key);
      }
      return Promise.resolve();
    }));
    await self.clients.claim();
  })());
});

async function trimCache(cache) {
  const keys = await cache.keys();
  const overflow = keys.length - MAX_CACHED_IMAGES;
  if (overflow <= 0) return;
  await Promise.all(keys.slice(0, overflow).map((request) => cache.delete(request)));
}

async function cacheImageUrl(url) {
  if (!/^https?:\/\//i.test(`${url || ""}`)) return;
  const cache = await caches.open(COMMANDER_IMAGE_CACHE);
  const request = new Request(url, { mode: "no-cors", credentials: "omit" });
  const existing = await cache.match(request);
  if (existing) return;
  try {
    const response = await fetch(request);
    if (!response) return;
    await cache.put(request, response.clone());
    await trimCache(cache);
  } catch {
    // Ignore cache warm failures; network may be unavailable.
  }
}

self.addEventListener("message", (event) => {
  const data = event.data || {};
  if (data.type !== "CACHE_IMAGES" || !Array.isArray(data.urls)) return;
  event.waitUntil(Promise.all(data.urls.map(cacheImageUrl)));
});

async function handleAppShellRequest(request) {
  const cache = await caches.open(APP_SHELL_CACHE);
  const cachedShell = await matchAppShellRequestAcrossCaches("./index.html");

  if (request.mode === "navigate") {
    try {
      const fresh = await fetch(request);
      if (fresh && fresh.ok) {
        await putAppShellResponse(cache, request, fresh.clone());
      }
      return await toCacheSafeResponse(fresh);
    } catch {
      if (cachedShell) return cachedShell;
      throw new Error("Offline and no cached app shell");
    }
  }

  const cached = await matchAppShellRequest(cache, request);
  if (cached) return cached;
  const cachedFromAnyShell = await matchAppShellRequestAcrossCaches(request);
  if (cachedFromAnyShell) return cachedFromAnyShell;

  try {
    const fresh = await fetch(request);
    if (fresh && fresh.ok && new URL(request.url).origin === self.location.origin) {
      await putAppShellResponse(cache, request, fresh.clone());
    }
    return fresh;
  } catch {
    const fallback = await matchAppShellRequestAcrossCaches(request);
    if (fallback) return fallback;
    throw new Error("Offline and no cached asset");
  }
}

self.addEventListener("fetch", (event) => {
  const request = event.request;
  if (request.method !== "GET") return;

  const url = new URL(request.url);

  if (url.origin === self.location.origin) {
    event.respondWith(handleAppShellRequest(request));
    return;
  }

  if (request.destination === "image" && /^https?:/i.test(request.url)) {
    event.respondWith((async () => {
      const cache = await caches.open(COMMANDER_IMAGE_CACHE);
      const cached = await cache.match(request);

      const networkFetch = fetch(request)
        .then(async (response) => {
          if (response) {
            await cache.put(request, response.clone());
            await trimCache(cache);
          }
          return response;
        })
        .catch(() => cached);

      return cached || networkFetch;
    })());
  }
});
