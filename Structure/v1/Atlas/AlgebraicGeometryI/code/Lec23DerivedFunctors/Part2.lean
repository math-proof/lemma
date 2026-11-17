/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec23DerivedFunctors
set_option maxHeartbeats 800000

open CategoryTheory Category Limits


public noncomputable section

universe v u

namespace Lec23

attribute [instance] DeltaFunctor.additive

/-- A (right) resolution of `M`: a cochain complex `K^•` together with a quasi-isomorphism
`(single₀ M) → K^•`. -/
structure Resolution {C : Type u} [Category.{v} C] [Abelian C] (M : C) where
  cocomplex : CochainComplex C ℕ
  [hasHomology : ∀ i, cocomplex.HasHomology i]
  ι : (CochainComplex.single₀ C).obj M ⟶ cocomplex
  quasiIso : QuasiIso ι := by infer_instance

end Lec23
end
