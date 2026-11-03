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

## Local setup that works: Lean 4.33.1, four steps

`build.sh` fetches nothing, and every file starts with `import Mathlib`, so a build needs (a) a
Lean 4.33.1 toolchain and (b) a Mathlib built by that same toolchain on `LEAN_PATH`.  One rule
behind all of it: `lean`, its `Init`, Mathlib and each dependency must come from a single
toolchain, because an `.olean` records the version *and* commit that built it; mixing them is the
`incompatible header` error.

The commands below use the checkout `Nextcloud/Progs/MyLEAN/DeficiencyOne`, relative to your home
directory; if your copy lives elsewhere, substitute that path — `elan override` records the
choice per directory, so it must be the directory you build in.

### 1. Install Mathlib v4.33.1 in a local directory

```bash
elan toolchain install leanprover/lean4:v4.33.1
cd Nextcloud/Progs/MyLEAN/DeficiencyOne     # this repo only, not the whole machine
elan override set leanprover/lean4:v4.33.1

git clone https://github.com/leanprover-community/mathlib4.git ~/mathlib4-433
cd ~/mathlib4-433
for c in $(git rev-list --all -- lean-toolchain | head -60); do
  [ "$(git show "$c:lean-toolchain" 2>/dev/null)" = "leanprover/lean4:v4.33.1" ] \
    && { git checkout "$c"; break; }
done
cat lean-toolchain && lake --version        # v4.33.1 in both
lake exe cache get                          # ~6 GB of prebuilt oleans, needs network
```

A clone of `master` pins whatever Mathlib currently uses, so the loop checks out a commit whose
`lean-toolchain` is `v4.33.1`; `lake --version` must report 4.33.1 as well, since that is the
toolchain `lake` belongs to.  `lake exe cache get` downloads oleans built for exactly that
commit — minutes instead of the hours a from-source Mathlib build takes.

### 2. Set the Lean version for the project directory

`elan override` is part of step 1; what it buys you is persistence — the choice is stored in
elan's own configuration, keyed by directory, so it survives closing the terminal and rebooting,
and it outranks the global default (`elan show` says which toolchain is active and why).  No
`lean-toolchain` file is added to the repository, which deliberately has none.

```bash
cd Nextcloud/Progs/MyLEAN/DeficiencyOne
elan override set leanprover/lean4:v4.33.1
lean --version                              # Lean (version 4.33.1, ...)
elan override unset                         # undo, when you want the global default back
```

### 3. Set LEAN_PATH

```bash
export LEAN_PATH="$(cd ~/mathlib4-433 && lake env printenv LEAN_PATH)"
```

This must be repeated in every new shell (put it in your shell's rc file to make it automatic).
`lake env printenv LEAN_PATH` lists the build directory of Mathlib and of each of its dependencies,
which is why it is asked of the Mathlib checkout rather than written out by hand.

### 4. Build project

```bash
cd Nextcloud/Progs/MyLEAN/DeficiencyOne
rm -rf .scratch/build && ELAN_NO_OVERRIDE_NOTICE=1 ./DeficiencyOne/build.sh
```

`rm -rf .scratch/build` first: those oleans belong to the toolchain that wrote them.
`ELAN_NO_OVERRIDE_NOTICE=1` just silences elan's per-invocation note that a directory override is
in force.  Expected result: exit 0, and exactly five `declaration uses 'sorry'` warnings — the
documented gaps listed in `DeficiencyOne/README.md`.
