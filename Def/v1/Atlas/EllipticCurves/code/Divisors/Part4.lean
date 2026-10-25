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
import Abbrev.v1.Atlas.EllipticCurves.code.Divisors.Part2


noncomputable section

open Finsupp

variable {P : Type*}

namespace CurveDiv

attribute [instance] FunctionFieldDiv.instCommGroup

variable (Φ : FunctionFieldDiv P)

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

end CurveDiv
end
