# Formalization

## Lean execution

```bash
(cd .lake/packages/mathlib && lake exe cache get)
export LEAN_PATH="$(cd .lake/packages/mathlib && lake env printenv LEAN_PATH)"
rm -rf .scratch/build 
./DeficiencyOne/build.sh
```

This seems to be the https://github.com/leanprover-community/mathlib4 repo.

```bash
cd /tmp
git clone https://github.com/leanprover-community/mathlib4.git
cd mathlib4/
lake exe cache get
```

```bash
cd /tmp/mathlib4/
export LEAN_PATH="$(lake env printenv LEAN_PATH)"
cd ~/Nextcloud/Progs/MyLEAN/DeficiencyOne
rm -rf .scratch/build 
./DeficiencyOne/build.sh
```

## On the Open Math OS VM: LEAN_PATH is already set, and Mathlib is read-only

The recipes above assume a **writable** Mathlib checkout belonging to the project, with Mathlib
nested at `.lake/packages/mathlib`. Neither holds on the VM, so the `lake` steps are not just
unnecessary there — they fail:

* Mathlib **is** `/opt/mathlib` (Lean 4.33.1, checked out from mathlib4, with the full build in
  `/opt/mathlib/.lake/build`, 6.5 GB, `Mathlib.olean` included). There is no
  `/opt/mathlib/.lake/packages/mathlib`; the dependencies (`batteries`, `aesop`, `Qq`, `Cli`,
  `proofwidgets`, `importGraph`, `LeanSearchClient`, `plausible`) sit beside it in
  `/opt/mathlib/.lake/packages/`.
* `/opt/mathlib` is owned by **root** and is not writable by the user the project runs as, and
  there is no `sudo`. Any `lake` command inside it therefore fails, e.g.

  ```console
  $ cd /opt/mathlib && lake env printenv LEAN_PATH
  info: plausible: URL has changed; deleting '/opt/mathlib/.lake/packages/plausible' and cloning again
  error: permission denied
  ```

  (Output trimmed; Lake's `error` names `PlausibleTest.lean` under `/opt/mathlib/.lake/packages`.)
  Lake reconciles the manifest before running anything, and the packaged checkouts have no
  `.git`, so it tries to re-clone them. Do not run `lake env`, `lake build` or `lake exe cache
  get` in `/opt/mathlib`.
* `LEAN_PATH` is **already exported** in every shell — `/opt/mathlib/.lake/build/lib/lean`, one
  entry per dependency, plus `/opt/cslib/.lake/build/lib/lean` and `/opt/lean/lib/lean`. So on the
  VM the whole procedure is:

  ```bash
  cd <repo>            # the project root, which is where shell commands start
  rm -rf .scratch/build
  ./DeficiencyOne/build.sh
  ```

  Note that this repository deliberately has **no `lakefile.lean` and no `lean-toolchain`**:
  `build.sh` drives `lean -o .scratch/build/... <file>.lean` directly and the files import each
  other by module name from the repository root. Nothing needs to be fetched or built twice; the
  oleans in `.scratch/build` are only a cache.

To check that the environment is sound before blaming the sources:

```bash
echo "$LEAN_PATH" | tr ':' '\n' | grep -qx /opt/mathlib/.lake/build/lib/lean && echo "Mathlib on LEAN_PATH"
mkdir -p .scratch/probe
printf 'import Mathlib\nexample : (2:ℚ) + 2 = 4 := by norm_num\n' > .scratch/probe/t.lean
lean .scratch/probe/t.lean        # about 2 s; writes nothing but .scratch/probe/t.olean
```

(The VM keeps `/tmp` in memory, so keep scratch files in the project's `.scratch/` instead.)

If you do need a Mathlib you can write to — a newer version, extra dependencies, or `lake exe
cache get` — build one **outside** `/opt`, under the shared home directory, and export its
`LEAN_PATH` instead. It costs about 6 GB and a few minutes:

```bash
git clone https://github.com/leanprover-community/mathlib4.git ~/mathlib4
cd ~/mathlib4
lake exe cache get                            # prebuilt oleans; needs network
export LEAN_PATH="$(lake env printenv LEAN_PATH)"   # now this works: the checkout is yours
cd <repo> && rm -rf .scratch/build && ./DeficiencyOne/build.sh
```

`~/mathlib4` is never cleaned (unlike `.scratch/`), so it survives; rebuild the project's own
`.scratch/build` afterwards, since oleans from a different Mathlib will not match.
