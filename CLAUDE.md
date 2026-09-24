# CLAUDE.md

## Docker pre-release process

When cutting a versioned pre-release from a Docker build that has already
been tested (e.g. a `ziskemu-v0.18.0-<sha>` image that passed the full EEST
corpus), don't push a new `docker/*` tag or dispatch `docker.yml` to get the
new version tag — that rebuilds from source and isn't guaranteed
byte-identical to what was actually tested. Instead, in this order:

1. **Retag the existing image digest** under the new semver tag, without
   rebuilding. Look up the digest via the registry API, not
   `docker manifest inspect -v` (which reports a per-platform manifest
   digest nested inside the index, not the index digest the registry treats
   as canonical for the tag):

   ```bash
   TOKEN=$(curl -s "https://ghcr.io/token?scope=repository:pirapira/stateless-pancaketh:pull" \
     | python3 -c "import sys,json;print(json.load(sys.stdin)['token'])")
   curl -s -D - -o manifest.json \
     -H "Authorization: Bearer $TOKEN" \
     -H "Accept: application/vnd.oci.image.index.v1+json" \
     "https://ghcr.io/v2/pirapira/stateless-pancaketh/manifests/<existing-tag>"
   # "docker-content-digest" response header is the canonical digest
   ```

   Then PUT that same manifest body under the new tag, using a push-scoped
   token (run `gh auth refresh -h github.com -s write:packages` first if the
   local `gh` token lacks `write:packages` — this needs interactive browser
   approval, so ask the user to run it):

   ```bash
   BEARER=$(curl -s -u "$(gh api user -q .login):$(gh auth token)" \
     "https://ghcr.io/token?scope=repository:pirapira/stateless-pancaketh:pull,push" \
     | python3 -c "import sys,json;print(json.load(sys.stdin)['token'])")
   curl -s -X PUT \
     -H "Authorization: Bearer $BEARER" \
     -H "Content-Type: application/vnd.oci.image.index.v1+json" \
     --data-binary @manifest.json \
     "https://ghcr.io/v2/pirapira/stateless-pancaketh/manifests/<new-tag>"
   ```

   No `buildx`/`skopeo`/`crane` needed.

2. **Update the README/docs** to reference the new tag, and land that as a
   normal PR.

3. **Only after that PR merges, tag the merged commit** with the release git
   tag (e.g. `git tag -a v0.1.0 -m ...`). Tagging last means the tagged
   commit's checked-out docs already match the retagged image, with no
   follow-up "point docs at the new tag" PR needed.

(v0.1.0 was cut out of this order — the commit was tagged before the docs PR
referencing `:v0.1.0` merged, so that tag's README still shows the older
sha-pinned tag. Not worth moving a pushed tag to fix retroactively, but
follow the order above next time.)
