const APP_SHELL_CACHE = "life-tracker-app-shell-v1";
const COMMANDER_IMAGE_CACHE = "life-tracker-commander-images-v1";
const MAX_CACHED_IMAGES = 180;

const APP_SHELL_ASSETS = [
  "./",
  "./index.html",
  "./style.css",
  "./app.js",
  "./manifest.webmanifest",
  "./icons/app-Icon.png",
  "./icons/favicon.png",
  "./icons/buttonshape.svg",
  "./icons/Back.svg",
  "./icons/Cancel.svg",
  "./icons/GameLog.svg",
  "./icons/JudyArrowHead.png",
  "./icons/Monarch.svg",
  "./icons/Ok.svg",
  "./icons/Pause.svg",
  "./icons/Play.svg",
  "./icons/Poison.svg",
  "./img/default_back0.png",
  "./img/default_back1.png",
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
  "./fonts/GoogleSansCode-SemiBoldItalic.woff"
];

self.addEventListener("install", (event) => {
  event.waitUntil((async () => {
    const cache = await caches.open(APP_SHELL_CACHE);
    await cache.addAll(APP_SHELL_ASSETS);
  })());
  self.skipWaiting();
});

self.addEventListener("activate", (event) => {
  event.waitUntil((async () => {
    const validCaches = new Set([APP_SHELL_CACHE, COMMANDER_IMAGE_CACHE]);
    const keys = await caches.keys();
    await Promise.all(keys.map((key) => {
      if (!validCaches.has(key)) {
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

  if (request.mode === "navigate") {
    try {
      const fresh = await fetch(request);
      if (fresh && fresh.ok) {
        await cache.put("./index.html", fresh.clone());
      }
      return fresh;
    } catch {
      const offlinePage = await cache.match("./index.html");
      if (offlinePage) return offlinePage;
      throw new Error("Offline and no cached app shell");
    }
  }

  const cached = await cache.match(request);
  if (cached) return cached;

  const fresh = await fetch(request);
  if (fresh && fresh.ok && new URL(request.url).origin === self.location.origin) {
    await cache.put(request, fresh.clone());
  }
  return fresh;
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
