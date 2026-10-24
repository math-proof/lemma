/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Units
import Mathlib.Algebra.Ring.GeomSum
import sympy.atlas.v1.Atlas.EllipticCurves.code.Divisors
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Divisors
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import sympy.atlas.v1.Atlas.EllipticCurves.code.TorsionEndomorphism

noncomputable section

open WeierstrassCurve.Affine

namespace WeilPairing

/-- Evaluation of a function `f : P → k` at a divisor `D = ∑ nₚ [P]`, producing the product
`∏ f(p) ^ nₚ` (Definition 23.18 in Sutherland's notes). -/
def functionEvalAtDivisor {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]
    (f : P → k) (D : P →₀ ℤ) : k :=
  D.prod (fun p n => f p ^ n)

/-- Weil reciprocity (Theorem 23.20): for functions `f, g` on a smooth projective curve whose
divisors have disjoint support, we have `f(div g) = g(div f)`. -/
noncomputable def lineFunction
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (P Q : W.Point) (R : W.Point) : F :=
  match P, Q, R with

  | .zero, _, _ => 1
  | _, .zero, _ => 1
  | _, _, .zero => 1

  | .some x₁ y₁ _, .some x₂ y₂ _, .some xR yR _ =>
    if x₁ = x₂ then
      if y₁ = y₂ then


        let denom := 2 * y₁ + W.a₁ * x₁ + W.a₃
        if denom = 0 then
          xR - x₁
        else
          let slope := (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / denom
          (yR - y₁) - slope * (xR - x₁)
      else

        xR - x₁
    else

      (yR - y₁) * (x₂ - x₁) - (xR - x₁) * (y₂ - y₁)

/-- The function `G_{P,Q} := L_{P,Q} / L_{P+Q, -(P+Q)}` from Definition 23.16, packaged as a
function into `Fˣ` and forced to `1` when the denominator/value vanishes. -/
noncomputable def lineFunctionG
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    W.Point → W.Point → (W.Point → Fˣ) :=
  fun P Q R =>
    let num := lineFunction W P Q R
    let den := lineFunction W (P + Q) (-(P + Q)) R


    if hd : den = 0 then 1
    else
      let val := num / den
      if hv : val = 0 then 1
      else Units.mk0 val hv

variable {F₀ : Type*} [Field F₀] [DecidableEq F₀]

/-- The divisor of the line `L_{P,Q}`, namely `[P] + [Q] + [-(P+Q)] - 3[0]`. -/
def divLine {W : WeierstrassCurve.Affine F₀} (P Q : W.Point) : W.Point →₀ ℤ :=
  Finsupp.single P 1 + Finsupp.single Q 1 + Finsupp.single (-(P + Q)) 1
    - 3 • Finsupp.single (0 : W.Point) 1

/-- The divisor of `G_{P,Q}`, namely `[P] + [Q] - [P+Q] - [0]`. -/
def divG {W : WeierstrassCurve.Affine F₀} (P Q : W.Point) : W.Point →₀ ℤ :=
  Finsupp.single P 1 + Finsupp.single Q 1 - Finsupp.single (P + Q) 1
    - Finsupp.single (0 : W.Point) 1

/-- Axiomatized "divisor of a function" map sending a function `W.Point → Fˣ` to its formal
divisor. Used as a placeholder for the algebraic-geometric `div` operator. -/
def LinearlyEquivalent {W : WeierstrassCurve.Affine F₀}
    (PrincE : AddSubgroup (W.Point →₀ ℤ))
    (D₁ D₂ : W.Point →₀ ℤ) : Prop :=
  D₁ - D₂ ∈ PrincE

section MillerFunction

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- The Miller function `f_{n,P}` for natural `n`, defined recursively (Definition 23.23):
`f_{0,P} = f_{1,P} = 1` and `f_{n+2,P} = f_{n+1,P} · G_{P, (n+1)P}`. -/
def millerFunctionNat (P : W.Point) : ℕ → (W.Point → Fˣ)
  | 0 => fun _ => 1
  | 1 => fun _ => 1
  | (n + 2) => fun R =>
    millerFunctionNat P (n + 1) R * lineFunctionG W P ((↑(n + 1) : ℤ) • P) R

/-- The Miller function `f_{n,P}` extended to all integers (Definition 23.23):
for `n < 0`, `f_{-n,P} := (f_{n,P} · G_{nP, -nP})⁻¹`. -/
def millerFunction (P : W.Point) (n : ℤ) : W.Point → Fˣ :=
  match n with
  | (m : ℕ) => millerFunctionNat W P m
  | Int.negSucc m =>
    fun R => (millerFunctionNat W P (m + 1) R *
              lineFunctionG W ((↑(m + 1) : ℤ) • P) (-(↑(m + 1) : ℤ) • P) R)⁻¹

/-- The divisor of `f_{n,P}`, namely `n[P] - (n-1)[0] - [nP]` (Lemma 23.24(i)). -/
def millerFunctionDivisor
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    W.Point → ℤ → (W.Point →₀ ℤ) :=
  fun P n =>
    n • Finsupp.single P 1 - (n - 1) • Finsupp.single (0 : W.Point) 1
      - Finsupp.single ((n : ℤ) • P) 1

/-- The group `μ_N(F)` of `N`-th roots of unity inside `Fˣ`. -/
def muN (N : ℕ) (F : Type*) [CommMonoid F] : Subgroup Fˣ :=
  rootsOfUnity N F

variable {F : Type*} [Field F] [DecidableEq F]

/-- The raw Weil pairing value (Lemma 23.26):
`e_n(P, Q) = f_{n,Q}(T) · f_{n,P}(Q - T) / (f_{n,P}(-T) · f_{n,Q}(P + T))`
for an auxiliary point `T`. -/
def weilPairingVal
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (N : ℕ) (P Q : W.Point) (T : W.Point) : Fˣ :=
  millerFunction W Q (N : ℤ) T *
    millerFunction W P (N : ℤ) (Q - T) *
  (millerFunction W P (N : ℤ) (-T) *
    millerFunction W Q (N : ℤ) (P + T))⁻¹

/-- The raw Weil pairing value `weilPairingVal W N P Q T` lies in `μ_N(F)` for `P, Q ∈ E[N]`
when `T` avoids the forbidden points `{0, Q, -P, Q - P}` (consequence of Lemma 23.21). -/
section Definition_23_19

variable {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]

/-- Divisor-level Weil pairing (Definition 23.19): given functions `f₁, f₂` representing the
`n`-torsion of the divisors `D₁, D₂` (i.e., `div fᵢ = n · Dᵢ`), define
`e_n(D₁, D₂) := f₁(D₂) / f₂(D₁)`. -/
def weilPairingDiv (f₁ f₂ : P → k) (D₁ D₂ : P →₀ ℤ) : k :=
  functionEvalAtDivisor f₁ D₂ * (functionEvalAtDivisor f₂ D₁)⁻¹

end Definition_23_19

section Lemma_23_21

variable {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]

/-- Bilinearity of the Weil pairing in the first argument (Theorem 23.29):
`e_N(P + Q, R) = e_N(P, R) · e_N(Q, R)`. -/
noncomputable def galoisActionOnMuN
    {F : Type*} [Field F] [DecidableEq F]
    (N : ℕ) (_hN : 0 < N) (_hchar : ¬ (ringChar F ∣ N))
    (σ : F ≃+* F) :
    ↥(muN N F) →* ↥(muN N F) where
  toFun := fun ⟨x, hx⟩ =>
    ⟨Units.map σ.toRingHom.toMonoidHom x, by
      simp only [muN, rootsOfUnity, Subgroup.mem_mk, Submonoid.mem_mk] at hx ⊢
      show (Units.map σ.toRingHom.toMonoidHom x) ^ N = 1
      rw [← map_pow, hx, map_one]⟩
  map_one' := by ext; simp [map_one]
  map_mul' := by intro a b; ext; simp [map_mul]

/-- Galois-equivariance of the Weil pairing (Theorem 23.29):
`e_N(σ·P, σ·Q) = σ·e_N(P, Q)` for every `σ ∈ Gal(F̄/F)`. -/
section EmbeddingDegree

variable {K : Type*} [Field K]

/-- The predicate "the `n`-torsion `E[n]` is contained in `E(L)`" for a field extension `L/K`
(used to define the embedding degree, Definition 23.32). -/
end EmbeddingDegree

section PairingFriendly

variable {K : Type*} [Field K]

/-- `W` is pairing-friendly for parameters `(n, k, bound)` if `k` is its embedding degree
with respect to `n` and `k ≤ bound` (small embedding degree makes the Tate pairing efficiently
computable in cryptographic applications). -/
end PairingFriendly

section TatePairing

/-- The Miller "double-and-add" algorithm: efficient evaluation of `f_{n,P}(Q)` using
`O(log n)` field operations (Corollary 23.25). At each step we either square the accumulator
(via the line `G_{mP, mP}`) or square and multiply by `G_{2mP, P}`. -/
def millerDoubleAndAdd (P : W.Point) (Q : W.Point) : ℕ → Fˣ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
    let m := (n + 2) / 2
    let acc := millerDoubleAndAdd P Q m

    let doubled := acc * acc * lineFunctionG W ((m : ℤ) • P) ((m : ℤ) • P) Q
    if (n + 2) % 2 = 0 then
      doubled
    else

      doubled * lineFunctionG W ((2 * m : ℤ) • P) ((1 : ℤ) • P) Q
  termination_by n => n

/-- Correctness of the Miller double-and-add algorithm:
`millerDoubleAndAdd W P Q n = f_{n,P}(Q)`. -/
def millerEvalCost : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    let m := (n + 2) / 2
    let sub_cost := millerEvalCost m
    if (n + 2) % 2 = 0 then
      sub_cost + 1
    else
      sub_cost + 2
  termination_by n => n

/-- Corollary 23.31, full-torsion case: if `P` has additive order `N` and together with `Q`
generates `E[N]`, then the Weil pairing `e_N(P, Q)` has order exactly `N` (so it is a primitive
`N`-th root of unity). -/
def IsSubgroupCyclicPair
    {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F}
    (P Q : W.Point) : Prop :=
  ∃ R : W.Point,
    AddSubgroup.closure ({P, Q} : Set W.Point) = AddSubgroup.zmultiples R

/-- Corollary 23.31 (one direction of the cyclic characterization):
if `e_N(P, Q) = 1` then `⟨P, Q⟩` is cyclic. -/
end Corollary_23_31

end WeilPairing
