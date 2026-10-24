/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFieldArith.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.FieldTheory.Perfect
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.FiniteFields
import Lemma.Complex.Atlas.v1.EllipticCurves.code.FiniteFields
import Mathlib.FieldTheory.Finite.Extension


namespace FiniteFieldArith

/-- The bit-size of a natural number `n`, defined as `⌊log₂ n⌋ + 1`. This is the
number of bits in the standard binary representation and serves as the cost
parameter `n = lg q` used throughout Sutherland's complexity analyses. -/
noncomputable def bitSize (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- Bit-operation cost of addition/subtraction in `𝔽_p`: linear in the bit-size
of `p`. The constant `3` is a small fixed overhead for carry propagation. -/
noncomputable def fpAddBitOps (p : ℕ) : ℕ := 3 * bitSize p

/-- Bit-operation cost of addition in `𝔽_q = 𝔽_{p^d}`: `d` independent additions
in `𝔽_p`, one per coefficient of the polynomial-basis representation. -/
noncomputable def fqAddBitOps (p d : ℕ) : ℕ := d * fpAddBitOps p

/-- Bit-operation cost of subtraction in `𝔽_q`: identical to addition. -/
noncomputable def fqSubBitOps (p d : ℕ) : ℕ := d * fpAddBitOps p

/-- The discrete Fourier transform `DFT_ω(f)(i) := f(ω^i)` at an element `ω ∈ R`
of order dividing `n`, returned as a function `Fin n → R`. Appears in
Theorem 3.29 / Theorem 3.30. -/
noncomputable def DFT (ω : R) (n : ℕ) (f : R[X]) : Fin n → R :=
  fun i => f.eval (ω ^ i.val)

/-- The cyclic convolution `(f * g) mod (X^n − 1)`. Used as the polynomial-level
operation diagonalised by the DFT in Theorem 3.29. -/
noncomputable def cyclicConv (n : ℕ) (f g : R[X]) : R[X] :=
  (f * g) %ₘ (X ^ n - 1)

/-- The "first half" of a polynomial `f`: the truncation `∑_{j < m} c_j X^j` of
`f` to degree `< m`. -/
noncomputable def polyFirstHalf (m : ℕ) (f : R[X]) : R[X] :=
  ∑ j ∈ Finset.range m, C (f.coeff j) * X ^ j

/-- The "second half" of a polynomial `f`: the coefficient sequence
`(f_m, f_{m+1}, …, f_{2m−1})` repackaged as a degree-`< m` polynomial. -/
noncomputable def polySecondHalf (m : ℕ) (f : R[X]) : R[X] :=
  ∑ j ∈ Finset.range m, C (f.coeff (m + j)) * X ^ j

/-- The twisted-difference polynomial `s_f(ω, m) := ∑_{j < m} (f_j − f_{m+j}) ω^j X^j`
that appears in the recursive FFT identity for odd-indexed DFT values. -/
noncomputable def fftTwistedDiff (ω : R) (m : ℕ) (f : R[X]) : R[X] :=
  ∑ j ∈ Finset.range m, C ((f.coeff j - f.coeff (m + j)) * ω ^ j) * X ^ j

/-- The radix-2 FFT (cf. Theorem 3.30): given a primitive `2^n`-th root of unity
`ω`, recursively computes `DFT_ω(f)(i)` for all `i < 2^n` using `O(n · 2^n)`
ring operations. -/
noncomputable def fft (ω : R) : (n : ℕ) → R[X] → (Fin (2 ^ n) → R)
  | 0, f => fun _ => f.eval 1
  | n + 1, f =>
    let m := 2 ^ n
    let r := polyFirstHalf m f + polySecondHalf m f
    let s := fftTwistedDiff ω m f
    let dft_r := fft (ω ^ 2) n r
    let dft_s := fft (ω ^ 2) n s
    fun i =>
      if i.val % 2 = 0 then
        dft_r ⟨i.val / 2, by have := i.isLt; simp only [pow_succ] at this; omega⟩
      else
        dft_s ⟨i.val / 2, by have := i.isLt; simp only [pow_succ] at this; omega⟩

/-- Predicate: `ω` is a primitive `2^n`-th root of unity in the radix-2 sense,
i.e. `ω^(2^(n−1)) = −1` (with the convention that the `n = 0` case is trivial).
This is the hypothesis under which the recursive FFT identities hold. -/
def IsPrim2PowRoot (ω : R) : ℕ → Prop
  | 0 => True
  | n + 1 => ω ^ (2 ^ n) = -1

/-- Operation count `5 · 2^k · k` for one radix-2 FFT of size `2^k` (Theorem 3.30). -/
def fftOpCount (k : ℕ) : ℕ := 5 * 2 ^ k * k

/-- Operation count `n` for pointwise multiplication of two `n`-vectors. -/
def pointwiseMulOpCount (n : ℕ) : ℕ := n

/-- Operation count `n` for computing `n` consecutive powers of an element. -/
def computePowersOpCount (n : ℕ) : ℕ := n

/-- Operation count `2n` for scalar multiplication of an `n`-vector. -/
def scalarMulOpCount (n : ℕ) : ℕ := 2 * n

/-- Total operation count for FFT-based polynomial multiplication at size `2^k`:
three FFTs plus pointwise multiplication, twiddle-power generation, and scalar
multiplications. This is the operation budget behind Corollary 3.31. -/
def fftPolyMulCost (k : ℕ) : ℕ :=
  let n := 2 ^ k
  3 * fftOpCount k + pointwiseMulOpCount n + 2 * computePowersOpCount n + scalarMulOpCount n

/-- Bit-length of a natural number `n`, using `Nat.size`. Equivalent to `bitSize`
but defined in terms of the standard library `Nat.size`. -/
def bitlength (n : ℕ) : ℕ := Nat.size n

variable (intMulCost : ℕ → ℕ)

/-- Cost model for modular reduction by an `n`-bit modulus using Newton-iteration
based fast division: `3 · M(n) + n` where `M(n) = intMulCost n`. -/
def modReductionCost (n : ℕ) : ℕ :=
  3 * intMulCost n + n

/-- Cost of multiplication in `𝔽_p`: one integer multiplication plus one modular
reduction, both of bit-length `bitlength p`. -/
def fpMulCost (p : ℕ) : ℕ :=
  intMulCost (bitlength p) + modReductionCost intMulCost (bitlength p)

/-- Schoolbook (quadratic) integer-multiplication cost: `M(n) = n²`. -/
def schoolbookMulCost (n : ℕ) : ℕ := n ^ 2

/-- Recursive cost model for the half-GCD algorithm (Lehmer / Knuth-Schönhage):
`H(n+1) = 2 · H((n+1)/2) + M(n+1)` with `H(0) = 0`. Underlies the
`O(M(n) log n)` complexity of fast Euclidean algorithms. -/
def halfGcdCost (M : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * halfGcdCost M ((n + 1) / 2) + M (n + 1)

/-- Master-recurrence bound for the half-GCD cost: for monotone multiplication
cost `M`, there is a constant `C` such that `halfGcdCost M n ≤ C · M(n) · (log₂ n + 1)`. -/
def fpInvCost (n : ℕ) : ℕ :=
  halfGcdCost intMulCost n

/-- Theorem 3.40: inversion in `𝔽_p^×` takes `O(M(n) · log n)` bit operations
where `n = lg p`. Formalised as existence of a constant `C` with the asymptotic
bound for every prime `p`. -/
def LogEBoundedByLogP (K : ℕ) (p e : ℕ) : Prop :=
  Nat.log 2 e ≤ K * (Nat.log 2 p + 1)

/-- Cost of computing polynomial GCDs at length `n`, using the half-GCD algorithm
instantiated with a given polynomial-multiplication cost. -/
def polyGcdCost (polyMulCost : ℕ → ℕ) (n : ℕ) : ℕ :=
  halfGcdCost polyMulCost n

/-- Cost model for inversion in `𝔽_q = 𝔽_{p^e}`: the Kronecker substitution
converts polynomial inversion into integer inversion of bit-width
`e · (bitSize p + bitSize e)`, then a half-GCD-based integer inversion gives the
final `O(M(n) log n)` bound. -/
noncomputable def fqInvCost (p e : ℕ) : ℕ :=
  let kroneckerBitWidth := e * (bitSize p + bitSize e)
  2 * intMulCost kroneckerBitWidth * (Nat.log 2 e + 1)

end FiniteFieldArith

namespace FiniteFieldArith

variable (intMulCost : ℕ → ℕ)

open Polynomial in
/-- Bit-width of the Kronecker substitution used to reduce multiplication in
`𝔽_{p^e}` to a single integer multiplication: `e · (2 · bitSize p + bitSize e)`. -/
noncomputable def kroneckerBitWidth (p e : ℕ) : ℕ :=
  e * (2 * bitSize p + bitSize e)

/-- Cost model for multiplication in `𝔽_q = 𝔽_{p^e}` via Kronecker substitution:
one integer multiplication of bit-width `kroneckerBitWidth p e`, plus a coefficient
extraction step costing `kroneckerBitWidth p e` bit operations. -/
noncomputable def fqMulCost (p e : ℕ) : ℕ :=
  2 * intMulCost (kroneckerBitWidth p e) + kroneckerBitWidth p e

/-- Helper for the bit-by-bit long-division algorithm (Algorithm 3.37): at bit
index `k`, with current quotient `q` and remainder `r`, perform the shift-and-
conditional-subtract step using the `k`-th bit of `a` against modulus `b`. -/
def longDivAux (a b : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, q, r =>
    if 2 * r + (a.testBit 0).toNat ≥ b then
      (2 * q + 1, 2 * r + (a.testBit 0).toNat - b)
    else
      (2 * q, 2 * r + (a.testBit 0).toNat)
  | k + 1, q, r =>
    if 2 * r + (a.testBit (k + 1)).toNat ≥ b then
      longDivAux a b k (2 * q + 1) (2 * r + (a.testBit (k + 1)).toNat - b)
    else
      longDivAux a b k (2 * q) (2 * r + (a.testBit (k + 1)).toNat)

/-- Algorithm 3.37 (long division): given naturals `a, b`, return a pair `(q, r)`
with `a = qb + r` and `0 ≤ r < b`, handling the edge cases `b = 0`, `b > a`, and
`b = 1` directly. -/
def longDiv (a b : ℕ) : ℕ × ℕ :=
  if b = 0 then (0, a)
  else if b > a then (0, a)
  else if b = 1 then (a, 0)
  else longDivAux a b (Nat.log 2 a) 0 0

/-- Bit-operation cost model for long division of an `m`-bit integer by an
`n`-bit integer: `3 · m · n`. -/
noncomputable def longDivCost (m n : ℕ) : ℕ := 3 * m * n
/-- The "different type" predicate from Theorem 3.44 (Rabin 1980): two nonzero
elements `a, b ∈ 𝔽_q` (with char ≠ 2) have different type when their
`(q−1)/2`-th powers disagree, i.e. one is a square and the other is not. Used in
the root-finding Algorithm 3.45. -/
def AreDifferentType (hF : ringChar F ≠ 2) (a b : F) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ (Fintype.card F / 2) ≠ b ^ (Fintype.card F / 2)

/-- Decidability of `AreDifferentType`: each of the three conditions
(`a ≠ 0`, `b ≠ 0`, distinct `(q−1)/2`-th powers) is decidable in a finite field. -/
instance (hF : ringChar F ≠ 2) (a b : F) : Decidable (AreDifferentType hF a b) := by
  unfold AreDifferentType; exact instDecidableAnd


namespace Polynomial

section SqfreeFactorization

variable {k : Type*} [Field k]
open Classical

/-- Squarefree factorization data (Algorithm 3.46): a polynomial `f` is given a
squarefree factorization as `f = ∏_{i < m} g_i^{i+1}` where the `g_i` are
pairwise coprime squarefree polynomials, `m > 0`, and the top exponent factor
`g_{m-1}` is not the constant `1`. -/
structure IsSquarefreeFactorization (f : k[X]) (m : ℕ) (gs : Fin m → k[X]) : Prop where
  pos : 0 < m
  prod_eq : f = ∏ i : Fin m, (gs i) ^ (i.val + 1)
  squarefree : ∀ i : Fin m, Squarefree (gs i)
  coprime : ∀ i j : Fin m, i ≠ j → IsCoprime (gs i) (gs j)
  last_ne_one : gs ⟨m - 1, Nat.sub_one_lt_of_lt pos⟩ ≠ 1

/-- Loop state for Yun's algorithm (Algorithm 3.46): the running pair `(v_i, w_i)`
of polynomials whose GCD with the derivative-difference yields the next factor `g_i`. -/
structure YunState (k : Type*) [Field k] where
  v : k[X]
  w : k[X]

/-- One iteration of Yun's algorithm: from state `(v, w)`, compute
`g = gcd(v, w − v')`, then advance to the new state `(v/g, (w − v')/g)`. -/
noncomputable def yunStep (st : YunState k) : k[X] × YunState k :=
  let diff := st.w - derivative st.v
  let g := EuclideanDomain.gcd st.v diff
  let v_new := st.v / g
  let w_new := diff / g
  (g, ⟨v_new, w_new⟩)

/-- Initialization of Yun's algorithm: from input `f`, divide out `u = gcd(f, f')`
to set `v_1 = f/u` and `w_1 = f'/u`. -/
noncomputable def yunInit (f : k[X]) : YunState k :=
  let u := EuclideanDomain.gcd f (derivative f)
  ⟨f / u, derivative f / u⟩

/-- Iterate Yun's algorithm for a bounded number of steps `n`, collecting the
factor sequence `g_1, g_2, …`. Stops early when the current `v_i` equals the
computed `g_i`. -/
noncomputable def yunIterate (st : YunState k) : ℕ → List (k[X]) × YunState k
  | 0 => ([], st)
  | n + 1 =>
    let (g, st') := yunStep st
    if st.v = g then ([g], st')
    else
      let (gs, st'') := yunIterate st' n
      (g :: gs, st'')

/-- Top-level Yun's algorithm (Algorithm 3.46): start from `f`, initialize, and
iterate for at most `fuel` steps, returning the list of squarefree factors
`g_1, g_2, …, g_m`. -/
noncomputable def yunAlgorithm (f : k[X]) (fuel : ℕ) : List (k[X]) :=
  (yunIterate (yunInit f) fuel).1

/-- The polynomial `X^{q^j} - X` over a finite field `k` of cardinality `q`.
Its roots are exactly the elements of the unique subfield `𝔽_{q^j} ⊆ k̄`, so its
factorization isolates irreducibles of degree dividing `j`. Used in
Algorithm 3.47 / Algorithm 3.46 for distinct-degree factorization. -/
noncomputable def xPowCardPowSubX (k : Type*) [Field k] [Fintype k] (j : ℕ) : k[X] :=
  X ^ (Fintype.card k) ^ j - X

/-- One step of distinct-degree factorization: from `f`, compute
`g = gcd(f, X^{q^j} − X)` (the product of degree-`j` irreducible factors of `f`)
and the new remaining polynomial `f / g`. -/
noncomputable def distinctDegreeStep (f : k[X]) (j : ℕ) : k[X] × k[X] :=
  let g := EuclideanDomain.gcd f (xPowCardPowSubX k j)
  (g, f / g)

/-- State for the distinct-degree factorization loop: the polynomial still left
to factor and the list of degree-`j` partial products accumulated so far. -/
structure DistinctDegreeState (k : Type*) [Field k] where
  remaining : k[X]
  factors : List (k[X])

/-- A single iteration of the distinct-degree factorization loop: extract the
product of degree-`j` irreducible factors of the current `remaining`, and append
it to the factor list. -/
noncomputable def distinctDegreeIter (st : DistinctDegreeState k) (j : ℕ) :
    DistinctDegreeState k :=
  let g := EuclideanDomain.gcd st.remaining (xPowCardPowSubX k j)
  { remaining := st.remaining / g
    factors := st.factors ++ [g] }

/-- Iterate distinct-degree factorization for `j = 1, 2, …, n`, starting from `f`. -/
noncomputable def distinctDegreeLoop (f : k[X]) : ℕ → DistinctDegreeState k
  | 0 => { remaining := f, factors := [] }
  | n + 1 => distinctDegreeIter (distinctDegreeLoop f n) (n + 1)

/-- Top-level distinct-degree factorization (step 2 of Algorithm 3.47): for input
`f`, run the loop up to degree `deg f` and return the list of degree-`j` factors. -/
noncomputable def distinctDegreeFactorize (f : k[X]) : List (k[X]) :=
  (distinctDegreeLoop f f.natDegree).factors

/-- Distinct-degree factorization specification (step 2 of Algorithm 3.47):
`f` factors as `∏ h_j` where each `h_j` is a (possibly trivial) squarefree
product of irreducibles all of degree `j+1`, and the `h_j` are pairwise coprime. -/
structure IsDistinctDegreeFactorization (f : k[X]) (d : ℕ) (hs : Fin d → k[X]) : Prop where
  prod_eq : f = ∏ i : Fin d, hs i
  irred_deg : ∀ (j : Fin d) (g : k[X]), Irreducible g → g ∣ hs j → g.natDegree = j.val + 1
  squarefree : ∀ j : Fin d, hs j = 1 ∨ Squarefree (hs j)
  coprime : ∀ i j : Fin d, i ≠ j → IsCoprime (hs i) (hs j)

/-- Correctness of distinct-degree factorization (step 2 of Algorithm 3.47): for
any monic squarefree polynomial `f` over a finite field, there exist `d` and
factors `h_0, …, h_{d-1}` with the `IsDistinctDegreeFactorization` property. -/
end DistinctDegreeFactorization

end Polynomial
