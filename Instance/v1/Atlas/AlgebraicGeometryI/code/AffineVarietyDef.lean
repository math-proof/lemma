/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Over
import Class.v1.Atlas.AlgebraicGeometryI.code.AffineVarietyDef


namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry CategoryTheory

universe u

/-- A `k`-algebra `A` gives `Spec A` the structure of a scheme over `Spec k` via the structure map
of the algebra. -/
noncomputable instance specOverSpec (k : Type u) [Field k] (A : Type u) [CommRing A]
    [Algebra k A] : (Spec (.of A)).Over (Spec (.of k)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap k A))⟩

/-- For `A` a reduced finitely-generated `k`-algebra, `Spec A` is an affine variety over `k`. -/
noncomputable instance specIsAffineVariety (k : Type u) [Field k] (A : Type u) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [_root_.IsReduced A] :
    IsAffineVariety k (Spec (.of A)) where
  toSpecΓ_isIso := (isAffine_Spec _).1
  locallyOfFiniteType := by
    rw [show (Spec (.of A) ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k A))
      from rfl]
    exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) |>.mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  isReduced := inferInstance

end AlgebraicGeometry.Scheme
