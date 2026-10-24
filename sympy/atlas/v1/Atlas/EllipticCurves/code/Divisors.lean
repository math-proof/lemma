/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

noncomputable section

open Finsupp

variable {P : Type*}

/-- The group of divisors on a curve (with point type `P`): the free abelian
group on `P`, modeled as `P →₀ ℤ`. Cf. Definition 23.13 (Sutherland §23.2): a
divisor is a finite formal sum `D = ∑_P n_P [P]` of points with integer
coefficients. -/
abbrev CurveDiv (P : Type*) := P →₀ ℤ

namespace CurveDiv

/-- The divisor `[p]` consisting of a single point with multiplicity `1`. -/
def of (p : P) : CurveDiv P := Finsupp.single p 1

/-- The coefficient (valuation) of `D` at `p`: this is `v_P(D)` in the notation
of Definition 23.13. -/
def coeff (D : CurveDiv P) (p : P) : ℤ := D p

/-- The support of a divisor `D`: the finite set of points where its coefficient
is nonzero. Cf. Definition 23.13. -/
def supp (D : CurveDiv P) : Finset P := D.support

/-- The degree of a divisor: `deg D := ∑_P v_P(D)` (Definition 23.13). -/
def deg (D : CurveDiv P) : ℤ := D.sum (fun _ n => n)

/-- The degree of the zero divisor is zero. -/
@[simp]
theorem deg_zero : deg (0 : CurveDiv P) = 0 := by
  simp [deg, Finsupp.sum]

/-- The degree of a single-point divisor `n[p]` is `n`. -/
@[simp]
theorem deg_single [DecidableEq P] (p : P) (n : ℤ) :
    deg (Finsupp.single p n) = n := by
  simp [deg, Finsupp.sum_single_index]

/-- Additivity of the degree: `deg(D₁ + D₂) = deg D₁ + deg D₂`. -/
theorem deg_add (D₁ D₂ : CurveDiv P) :
    (D₁ + D₂).deg = D₁.deg + D₂.deg := by
  classical
  simp only [deg]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- The degree map `Div C → ℤ` packaged as an additive group homomorphism. -/
def degHom (P : Type*) : CurveDiv P →+ ℤ where
  toFun := deg
  map_zero' := deg_zero
  map_add' := deg_add

/-- The subgroup `Div⁰ C` of divisors of degree zero, defined as the kernel of
the degree map. (Cf. Definition 23.13.) -/
def DivZero (P : Type*) : AddSubgroup (CurveDiv P) :=
  AddMonoidHom.ker (degHom P)

/-- Membership in `DivZero P` is equivalent to having degree zero. -/
theorem mem_divZero_iff (D : CurveDiv P) :
    D ∈ DivZero P ↔ D.deg = 0 := by
  simp [DivZero, degHom, AddMonoidHom.mem_ker]

/-- A "function-field-with-divisor-map" structure: a multiplicative group `F`
(intended to be the function field `k(C)^×`), a subgroup `kUnits` of constants
`k^×`, and a group homomorphism `divMap : (F, ·) → (Div C, +)` sending each
nonzero function to its principal divisor `div f`. -/
structure FunctionFieldDiv (P : Type*) where
  F : Type*
  [instCommGroup : CommGroup F]
  kUnits : Subgroup F
  divMap : Additive F →+ CurveDiv P

attribute [instance] FunctionFieldDiv.instCommGroup

/-- Every principal divisor has degree zero (Corollary 23.10 / Definition
23.13). -/
variable (Φ : FunctionFieldDiv P)

/-- The subgroup `Princ C ⊆ Div C` of principal divisors, defined as the image
of the function-field divisor map. (Definition 23.13.) -/
def PrincDiv : AddSubgroup (CurveDiv P) :=
  AddMonoidHom.range Φ.divMap

/-- Principal divisors are divisors of degree zero. -/
abbrev PicardGroup : Type _ :=
  CurveDiv P ⧸ PrincDiv Φ

/-- Since principal divisors have degree zero, the degree map descends to a
homomorphism `Pic C → ℤ` from the Picard group. -/
abbrev PicardGroupZero : Type _ :=
  (DivZero P) ⧸ (PrincDiv Φ).addSubgroupOf (DivZero P)

section AbelJacobi

variable {P : Type*}

/-- The degree-zero divisor `[p] - [O]` for the Abel-Jacobi map with origin
`O` (Definition 23.15). -/
def abelJacobiDivAt (O : P) (p : P) : DivZero P :=
  ⟨Finsupp.single p 1 - Finsupp.single O 1,
   (mem_divZero_iff _).mpr (by
     classical
     show (degHom P) _ = 0
     simp [degHom, map_sub, deg_single])⟩

/-- The Abel-Jacobi map `P ↦ [p] - [O]` modulo principal divisors, as a function
`P → Pic⁰ C` (Definition 23.15). -/
def abelJacobiMapAt (Φ : FunctionFieldDiv P) (O : P) (p : P) : PicardGroupZero Φ :=
  QuotientAddGroup.mk (abelJacobiDivAt O p)

end AbelJacobi

/-- For `P` an abelian group, the *point sum* of a divisor `∑ n_P [P]` is
`∑ n_P · P`, interpreted in the group `P`. For elliptic curves this is the map
`Div E → E` induced by the group law. -/
def pointSum [AddCommGroup P] (D : CurveDiv P) : P :=
  D.sum (fun p n => n • p)

/-- `pointSum` packaged as an additive group homomorphism `Div C → P`. -/
def pointSumHom (P : Type*) [AddCommGroup P] : CurveDiv P →+ P where
  toFun := pointSum
  map_zero' := by simp [pointSum, Finsupp.sum]
  map_add' D₁ D₂ := by
    classical
    simp only [pointSum]
    exact Finsupp.sum_add_index' (fun _ => zero_zsmul _) (fun _ _ _ => add_zsmul _ _ _)

/-- A divisor on an elliptic curve (group `P`) is principal iff it has degree
zero and its point-sum vanishes. This is the standard "sum-to-zero" criterion
for principal divisors (cf. Theorem 23.17). -/
def abelJacobiDiv (p : P) : DivZero P := abelJacobiDivAt 0 p

/-- The point-sum map restricted to degree-zero divisors, as an additive group
homomorphism `Div⁰ C → P`. -/
def pointSumHomDivZero : DivZero P →+ P :=
  (pointSumHom P).comp (DivZero P).subtype

/-- The point-sum map descends to `Pic⁰ C → P` since principal divisors have
zero point-sum; this is the *inverse* of the Abel-Jacobi isomorphism. -/
end CurveDiv

noncomputable section

/-- A smooth projective curve, represented abstractly by a type of points
`Point`, a function field `FunctionField` (a field), and a discrete-valuation
map `val P : FunctionField → WithTop ℤ` at each point `P` satisfying the
standard axioms of a normalized valuation: `val P 0 = ⊤`, `val P 1 = 0`,
`val P (fg) = val P f + val P g`, `val P (f+g) ≥ min (val P f) (val P g)`,
finiteness at nonzero elements, and surjectivity onto `ℤ`. -/
structure SmoothProjectiveCurve where
  Point : Type*
  FunctionField : Type*
  [fieldInst : Field FunctionField]
  val : Point → FunctionField → WithTop ℤ
  val_zero : ∀ P, val P 0 = ⊤
  val_one : ∀ P, val P 1 = 0
  val_mul : ∀ P f g, val P (f * g) = val P f + val P g
  val_add : ∀ P f g, min (val P f) (val P g) ≤ val P (f + g)
  val_ne_top : ∀ P (f : FunctionField), f ≠ 0 → val P f ≠ ⊤
  val_surj : ∀ P (n : ℤ), ∃ f : FunctionField, f ≠ 0 ∧ val P f = ↑n

attribute [instance] SmoothProjectiveCurve.fieldInst

/-- A morphism `C → ℙ¹` from a smooth projective curve, recorded via a chosen
function `f`, its degree, and the (finite) fiber over each point of `ℙ¹`. The
`uniformizerComp Q` represents the uniformizer at `Q ∈ ℙ¹` pulled back to a
function on `C`. -/
structure MorphismToP1 (C : SmoothProjectiveCurve) where
  f : C.FunctionField
  f_ne_zero : f ≠ 0
  deg : ℤ
  deg_pos : 0 < deg
  P1Point : Type*
  uniformizerComp : P1Point → C.FunctionField
  uniformizerComp_ne_zero : ∀ Q, uniformizerComp Q ≠ 0
  fiber : P1Point → Finset C.Point
  mem_fiber_iff : ∀ Q (P : C.Point),
    P ∈ fiber Q ↔ (0 : WithTop ℤ) < C.val P (uniformizerComp Q)

/-- The degree of a morphism `φ : C → ℙ¹` equals the sum, over the points `P` in
the fiber over `Q`, of the valuation `v_P(uniformizerComp Q)`. This is the
content of the degree-fiber formula for morphisms to `ℙ¹`. -/
structure RationalMap (C : SmoothProjectiveCurve) (m : ℕ) where
  coords : Fin m → C.FunctionField
  not_all_zero : ∃ i, coords i ≠ 0

/-- A rational map is *defined at* a point `P` if there exists a rescaling
`c ∈ k(C)^×` so that every coordinate `c · coords i` has nonnegative valuation
at `P` and at least one has valuation zero. -/
def RationalMap.isDefinedAt {C : SmoothProjectiveCurve} {m : ℕ}
    (φ : RationalMap C m) (P : C.Point) : Prop :=
  ∃ (c : C.FunctionField), c ≠ 0 ∧
    (∀ i, (0 : WithTop ℤ) ≤ C.val P (c * φ.coords i)) ∧
    (∃ i, C.val P (c * φ.coords i) = 0)

/-- A rational map is a *morphism* if it is defined at every point. -/
def RationalMap.isMorphism {C : SmoothProjectiveCurve} {m : ℕ}
    (φ : RationalMap C m) : Prop :=
  ∀ P : C.Point, φ.isDefinedAt P
