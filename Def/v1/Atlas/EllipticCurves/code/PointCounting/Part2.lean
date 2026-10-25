/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PointCounting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Exponent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Real.Pi.Bounds
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Instance.v1.Atlas.EllipticCurves.code.PointCounting


section Lemma71

variable {R : Type*} [Ring R] (IsInsep : R → Prop)

variable {IsInsep}

/-- The number $\#E(\mathbb{F}_q)$ of $\mathbb{F}_q$-rational points (including the point
at infinity) of a Weierstrass curve over a finite field. -/
noncomputable def numPoints (W : WeierstrassCurve.Affine F) : ℕ :=
  Fintype.card W.Point

/-- The trace of Frobenius $t = q + 1 - \#E(\mathbb{F}_q)$ for an elliptic curve $E$
over $\mathbb{F}_q$. By Hasse's theorem, $|t| \leq 2\sqrt{q}$. -/
noncomputable def traceFrobenius (W : WeierstrassCurve.Affine F) : ℤ :=
  (Fintype.card F : ℤ) + 1 - (numPoints W : ℤ)

/-- The exponent of a group $G$: the least $n$ such that $g^n = 1$ for all $g \in G$
(equivalent to the LCM of orders of elements when $G$ is finite). -/
noncomputable def groupExponent : ℕ := Monoid.exponent G

end GroupExponent

section EulerProductInfra

/-- The completely multiplicative monoid-with-zero homomorphism $\mathbb{N} \to \mathbb{R}$
sending $n \mapsto 1/n^2$ (and $0 \mapsto 0$). Used to express $\zeta(2)$ as the Euler
product $\sum_n 1/n^2 = \prod_p (1 - p^{-2})^{-1}$. -/
noncomputable def oneOverSqHom : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else 1 / (n : ℝ) ^ 2
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [hm, hn, Nat.mul_eq_zero, or_self, ↓reduceIte, Nat.cast_mul]; field_simp

open scoped Classical in
open Finset in
/-- The number of "good" pairs $(g_1, g_2) \in G \times G$ such that
$\mathrm{lcm}(\mathrm{ord}(g_1), \mathrm{ord}(g_2))$ equals the exponent of $G$. This
counts pairs that together generate a cyclic subgroup of order equal to the exponent. -/
noncomputable def numGoodPairs (G : Type*) [CommGroup G] [Fintype G] : ℕ :=
  (univ : Finset (G × G)).filter
    (fun p => Nat.lcm (orderOf p.1) (orderOf p.2) = Monoid.exponent G) |>.card

/-- The probability that two random elements of $G$ have orders whose LCM equals the
exponent of $G$: $|\text{good pairs}| / |G|^2$. -/
noncomputable def probLcmEqExponent (G : Type*) [CommGroup G] [Fintype G] : ℝ :=
  (numGoodPairs G : ℝ) / (Fintype.card G : ℝ) ^ 2

/-- Iteratively divide $m$ by $p$ as long as the smaller multiple $m/p$ still
annihilates the point $P$. This is the key subroutine in Algorithm 7.4 (order
computation): given any annihilator $m$, it strips the prime $p$ to obtain a smaller
annihilator. -/
noncomputable def stripPrimeFactor (P : G) (p : ℕ) (hp : 1 < p) : ℕ → ℕ
  | m =>
    if hcond : 0 < m ∧ p ∣ m ∧ (m / p) • P = 0 then
      have : m / p < m := Nat.div_lt_self hcond.1 hp
      stripPrimeFactor P p hp (m / p)
    else m
termination_by m => m

/-- Algorithm 7.4: compute the order of a point $P$ in an additive group given a known
multiple $m$ and a list of primes containing all prime factors of the order. Strips each
prime in turn via `stripPrimeFactor`. -/
noncomputable def computeOrder (P : G) : List ℕ → ℕ → ℕ
  | [], m => m
  | p :: ps, m =>
    if hp : 1 < p then computeOrder P ps (stripPrimeFactor P p hp m)
    else computeOrder P ps m

/-- Two Weierstrass curves $E'$ and $E$ over $F$ are *twists* of each other if there is
a field extension $L/F$ over which they become isomorphic via a Weierstrass variable
change. -/
def IsTwistOf (E' E : WeierstrassCurve.Affine F) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra F L)
    (C : @WeierstrassCurve.VariableChange L _),
    C • (E.map (algebraMap F L)) = E'.map (algebraMap F L)

/-- The quadratic twist of a short Weierstrass curve $W : y^2 = x^3 + a_4 x + a_6$ by
$s \in F$: the curve $y^2 = x^3 + (s^2 a_4) x + (s^3 a_6)$. -/
noncomputable def quadraticTwistCurve (W : WeierstrassCurve.Affine F) (s : F) :
    WeierstrassCurve.Affine F :=
  ⟨0, 0, 0, s ^ 2 * W.a₄, s ^ 3 * W.a₆⟩

/-- The number of points on the quadratic twist of $W$ over $\mathbb{F}_q$, defined via
the relation $\#E + \#E^{\mathrm{twist}} = 2q + 2$. -/
noncomputable def twistNumPoints {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) : ℕ :=
  2 * Fintype.card F + 2 - Hasse.numPoints W

/-- The predicate "$N$ has a unique positive multiple in the closed interval
$[\mathit{lo}, \mathit{hi}]$": there is exactly one positive integer $k$ such that
$\mathit{lo} \leq k N \leq \mathit{hi}$. Mestre's theorem uses this to pin down the
number of points from a known annihilator. -/
def HasUniqueMultipleIn (N : ℕ) (lo hi : ℝ) : Prop :=
  ∃! k : ℕ, 0 < k ∧ lo ≤ (k * N : ℝ) ∧ (k * N : ℝ) ≤ hi

end EulerProductInfra
