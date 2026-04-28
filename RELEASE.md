# v0.1.0 release checklist

The repo is now in the state I can take it to: code polished, tests passing (384/384), docs site builds, license + citation + workflows in place. The remaining steps are things that have to happen on your end (creating the GitHub repo, secrets, tags). This document walks through them in order.

## 1. Create the GitHub repo

Go to <https://github.com/new> and create:

- Owner: `aidanpetro1`
- Repository name: `Poly.jl`
- Visibility: Public
- Do **not** initialize with a README, .gitignore, or license — we have those locally already.

If you pick a different name or owner, you'll need to update the repo URL in three places:

- `docs/make.jl` — the `REPO` constant near the top
- `README.md` — badge URLs and install instructions
- `CITATION.cff` — the `repository-code` field

## 2. Initialize git locally and push

From `C:\Polynomial`:

```sh
git init
git add .
git commit -m "Initial commit: Poly.jl v0.1.0"
git branch -M main
git remote add origin git@github.com:aidanpetro1/Poly.jl.git
git push -u origin main
```

Confirm CI runs: <https://github.com/aidanpetro1/Poly.jl/actions>. The `CI` workflow should pass on Linux/macOS/Windows × Julia 1.10/1. Allow ~5 minutes.

## 3. Set up the Documenter deploy key

Documenter pushes the rendered docs site to a `gh-pages` branch. It needs an SSH keypair where the public key is a deploy key on the repo and the private key is a repo secret named `DOCUMENTER_KEY`.

Run it as two Julia calls — `using DocumenterTools` in the same `-e` block as `Pkg.add` fails because the loader resolves `using` before `Pkg.add` runs:

```sh
julia -e 'using Pkg; Pkg.add("DocumenterTools")'
julia -e 'using DocumenterTools; DocumenterTools.genkeys(user="aidanpetro1", repo="Poly.jl")'
```

The second call prints two things:

1. A **public key** — go to <https://github.com/aidanpetro1/Poly.jl/settings/keys/new>, paste it, name it "DOCUMENTER_KEY", and **check "Allow write access"**.

2. A **private key** — go to <https://github.com/aidanpetro1/Poly.jl/settings/secrets/actions/new>, name it `DOCUMENTER_KEY` exactly, paste the private key value.

Push any commit to trigger the `Documenter` workflow. After it succeeds the first time, GitHub will create the `gh-pages` branch automatically.

## 4. Turn on GitHub Pages

After the first successful Documenter run:

- Go to <https://github.com/aidanpetro1/Poly.jl/settings/pages>
- Source: "Deploy from a branch"
- Branch: `gh-pages` / `/ (root)`
- Save

The site will be live at <https://aidanpetro1.github.io/Poly.jl/dev/> within a minute or two. Once you tag a release (next step), `/stable/` will also resolve.

## 5. Tag v0.1.0

```sh
git tag -a v0.1.0 -m "Poly.jl v0.1.0"
git push origin v0.1.0
```

The Documenter workflow re-runs on tags and publishes a versioned `/v0.1.0/` doc set, plus updates `/stable/` to point at it.

## 6. (Optional) Codecov

The CI workflow already calls `codecov-action`, but it'll silently skip without a token. If you want coverage reports:

- Sign in at <https://codecov.io> with your GitHub account, add the repo.
- Copy the upload token, add it as a repo secret named `CODECOV_TOKEN`.

Skip this if you don't care about coverage — `continue-on-error: true` in the workflow means CI passes regardless.

## 7. (Later) Register with the General registry

We deliberately deferred this for v0.1.0 so you can iterate on the API without semver pressure. When you're ready (probably after the application project shakes out the public surface):

- Install the Registrator GitHub App on the repo: <https://github.com/JuliaRegistries/Registrator.jl>
- Comment `@JuliaRegistrator register` on the v0.1.0 release commit
- A bot will open a PR against the General registry; merging it makes `Pkg.add("Poly")` work for everyone

Until then, users install via the URL form shown in the README.

---

## Things to know

- **The `Manifest.toml` files are gitignored.** That's the Julia convention for libraries (apps commit them; libraries don't). Anyone cloning the repo runs `Pkg.instantiate()` to materialize a fresh resolution.

- **`docs/build/` is gitignored.** Documenter regenerates it on every build. Don't be surprised that the local build artifacts disappear from the working tree — they're still in `docs/build/` locally, just not tracked.

- **The placeholder UUID is gone.** The `uuid` in `Project.toml` is now `c6ac206a-14ad-4e46-bdab-7d10e8cbd250`. Don't change this — Julia's package system identifies packages by UUID, not by name, so once anyone has the v0.1.0 UUID they'll get matched to it forever.

- **The `▷ vs ◁` workaround is permanent.** Julia's parser doesn't accept `◁` as an operator and there's no opt-in to change that without dropping into a custom string-macro syntax. `▷` is what users will see; the book uses `◁`.
