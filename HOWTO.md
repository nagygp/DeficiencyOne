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

## Using Lean 4.33 locally, starting from no Mathlib

`build.sh` fetches nothing: every file imports `Mathlib`, so the build needs a Mathlib **built by
the same Lean** as the `lean` on `PATH`, and it says so and stops if `LEAN_PATH` is unset. The
one rule everything below serves: `lean`, `Init`, Mathlib and every dependency must come from a
single toolchain, because an `.olean` records the version *and* commit that produced it
(`strings -n 3 …/Init.olean | head -3`) and a mismatch is the `incompatible header` error.

1. **Pin the toolchain.** `elan toolchain install leanprover/lean4:v4.33.1`, then either
   `elan default leanprover/lean4:v4.33.1` (whole machine) or, better for one repository,
   `cd <repo> && elan override set leanprover/lean4:v4.33.1`. Confirm with `lean --version`
   (expect commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). No `lean-toolchain` file is added:
   the repository deliberately has none.

2. **Get a Mathlib built by that toolchain.** Any commit whose `lean-toolchain` reads
   `leanprover/lean4:v4.33.1` will do — the header pins the toolchain, not the sources:

   ```bash
   git clone https://github.com/leanprover-community/mathlib4.git ~/mathlib4-433
   cd ~/mathlib4-433
   for c in $(git rev-list --all -- lean-toolchain | head -60); do
     [ "$(git show "$c:lean-toolchain" 2>/dev/null)" = "leanprover/lean4:v4.33.1" ] \
       && { git checkout "$c"; break; }
   done
   cat lean-toolchain          # must print leanprover/lean4:v4.33.1
   lake --version              # must report (Lean version 4.33.1) — this is the toolchain of `lake`
   lake exe cache get          # prebuilt oleans for exactly this commit; needs network
   ```

   `lake env` prints the `LEAN_PATH` of `lake`'s **own** toolchain, so if the last line above
   shows a different Lean, `lean-toolchain` is not what you think it is (a fresh clone of
   `master` pins whatever Mathlib currently uses, regardless of the directory's name).

3. **Export and build.**

   ```bash
   export LEAN_PATH="$(cd ~/mathlib4-433 && lake env printenv LEAN_PATH)"
   cd <repo>
   rm -rf .scratch/build       # stale oleans carry the old version; always clear on switch
   ./DeficiencyOne/build.sh    # exit 0 and exactly five `declaration uses 'sorry'` warnings
   ```

Deterministic variant, if `PATH` or elan shims keep selecting the wrong `lake`:

```bash
export LEAN_PATH="$(~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake env printenv LEAN_PATH)"
```

Consistency check — the two commands must name the same version and commit:

```bash
lean --githash
strings -n 3 ~/.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean/Init.olean | head -3
```

The sources themselves are toolchain-neutral for the `if` renames: since commit `3b24b14`
`Defs.lean` states `ite_eq_of_pos`/`ite_eq_of_neg`/`dite_eq_of_pos`/`dite_eq_of_neg` and nothing
else mentions `if_pos`, `if_neg`, `ite_eq_left` or `ite_eq_right`.
