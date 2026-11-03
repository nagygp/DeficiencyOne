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