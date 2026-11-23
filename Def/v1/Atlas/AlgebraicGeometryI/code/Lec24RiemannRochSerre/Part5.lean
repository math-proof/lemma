/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityStatement
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityStatement
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre

@[expose] public section

set_option maxHeartbeats 800000


noncomputable section

namespace Lec24

namespace SmoothCompleteCurveWithSheaves

variable (X : SmoothCompleteCurveWithSheaves)

/-- The class `[F]` of a coherent sheaf `F` in `K_0(Coh X)`. -/
def K0Coh.classOf (X : SmoothCurveK0Data) (F : X.CohSheaf) : K0Coh X :=
  QuotientAddGroup.mk' (sesRelations X) (FreeAbelianGroup.of F)

/-- The group homomorphism `ℤ ⊕ ℤ → K_0(Coh X)` sending `(r, d) ↦ r·[O_X] + d·[O_x]`,
which is shown by Lemma 35 to be surjective. -/
def rankDegToK0 (X : SmoothCurveK0Data) : ℤ × ℤ →+ K0Coh X where
  toFun := fun ⟨r, d⟩ => r • K0Coh.classOf X X.O_X + d • K0Coh.classOf X X.O_x
  map_zero' := by simp
  map_add' := by intro ⟨r₁, d₁⟩ ⟨r₂, d₂⟩; simp [add_smul]; abel

/-- The arithmetic genus `p_a := 1 - χ(O_X)`. -/
def arithmeticGenus_pa : ℤ :=
  1 - X.chi X.structureSheaf

/-- The geometric genus `p_g := h⁰(ω_X)`. -/
def geometricGenus_pg : ℕ :=
  (X.data X.canonicalSheaf).h0

end SmoothCompleteCurveWithSheaves
end Lec24
end
