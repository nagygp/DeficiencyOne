"""Numerical sanity check for Lemma 4 (DeficiencyOne/Section2FixedPointBound.lean).

For a prime power q = p^k it searches random polynomials d over F_q of degree at most q - 1 and
counts the zeros of d', comparing the maximum with the bound  q - q/p - 1  of the paper.
Run with `python3 DeficiencyOne/lemma4_sanity.py` (needs no dependencies).

Sample output:
    q= 9 p=3 bound q-q/p-1 =  5   max zeros found by random search: 4   OK
    q=25 p=5 bound q-q/p-1 = 19   max zeros found by random search: 6   OK
    q=27 p=3 bound q-q/p-1 = 17   max zeros found by random search: 12   OK
    q=49 p=7 bound q-q/p-1 = 41   max zeros found by random search: 14   OK
    q= 7 p=7 bound q-q/p-1 =  5   max zeros found by random search: 5   OK
(the prime case attains the bound, as it must: there the bound is the root bound.)
"""
import itertools, random
random.seed(0)

def make_field(p, k, irr):
    # elements: tuples of length k (coeffs of 1, a, a^2, ...); irr: coeff list length k+1 (monic, degree k)
    els = list(itertools.product(range(p), repeat=k))
    idx = {e: i for i, e in enumerate(els)}
    q = len(els)
    def mul_poly(a, b):
        c = [0]*(len(a)+len(b)-1)
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                c[i+j] = (c[i+j] + ai*bj) % p
        # reduce mod irr (monic degree k)
        for d in range(len(c)-1, k-1, -1):
            co = c[d]
            if co:
                for j in range(k+1):
                    c[d-k+j] = (c[d-k+j] - co*irr[j]) % p
        return tuple(c[:k]) + tuple([0]*(k-len(c[:k])))
    mult = [[idx[mul_poly(a, b)] for b in els] for a in els]
    add  = [[idx[tuple((a[i]+b[i]) % p for i in range(k))] for b in els] for a in els]
    zero = idx[tuple([0]*k)]
    one  = idx[(1,)+tuple([0]*(k-1))]
    return els, add, mult, zero, one

def analyse(p, k, irr, trials=4000):
    els, add, mult, zero, one = make_field(p, k, irr)
    q = len(els)
    def evalpoly(coeffs, x):   # coeffs[i] = coeff of X^i (field index), Horner
        acc = zero
        for c in reversed(coeffs):
            acc = add[mult[acc][x]][c]
        return acc
    def deriv(coeffs):
        out = []
        for i in range(1, len(coeffs)):
            m = i % p                      # i as element of F_p
            out.append(mult[m][coeffs[i]] if m != 0 else zero)
        return out
    best = 0; bestd = None
    for _ in range(trials):
        deg = random.randint(2, q-1)
        d = [random.randrange(q) for _ in range(deg)] + [random.randrange(1, q)]
        g = deriv(d)
        if all(c == zero for c in g):
            continue
        z = sum(1 for x in range(q) if evalpoly(g, x) == zero)
        if z > best:
            best, bestd = z, d
    bound = q - q//p - 1
    print(f"q={q:2d} p={p} bound q-q/p-1 = {bound:2d}   max zeros found by random search: {best}"
          f"   {'OK' if best <= bound else 'VIOLATION'}")

analyse(3, 2, [1, 0, 1])      # F_9  = F_3[a]/(a^2+1)
analyse(5, 2, [2, 0, 1])      # F_25 = F_5[a]/(a^2+2)
analyse(3, 3, [1, 1, 0, 1])   # F_27 = F_3[a]/(a^3+a+1)
analyse(7, 2, [3, 0, 1])      # F_49 = F_7[a]/(a^2+3)
analyse(7, 1, [0, 1])         # F_7  (prime field)
analyse(2, 4, [1, 1, 0, 0, 1])# F_16 = F_2[a]/(a^4+a+1)  (even char, for comparison)
