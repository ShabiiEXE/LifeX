const COMMANDER_IMAGE_CACHE = "life-tracker-commander-images-v1";
const MAX_CACHED_IMAGES = 180;

self.addEventListener("install", () => {
  self.skipWaiting();
});

self.addEventListener("activate", (event) => {
  event.waitUntil(self.clients.claim());
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

self.addEventListener("fetch", (event) => {
  const request = event.request;
  if (request.method !== "GET") return;
  if (request.destination !== "image") return;
  if (!/^https?:/i.test(request.url)) return;

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
});
