/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafDef
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.TwistSheaf
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf.Part2
import Instance.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part2


noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section MvPolynomialSmooth

variable (k : Type u) [Field k] (n : ℕ)

/-- Type of graded `k`-linear maps in fixed degree `d` between two graded modules `M`, `N`. -/
abbrev GrLinMap (M N : GradedModuleData.{u, u} k n) (d : ℤ) : Type u :=
  @LinearMap k k _ _ (RingHom.id k) (M.component d) (N.component d)
    (M.instACG d).toAddCommMonoid (N.instACG d).toAddCommMonoid (M.instMod d) (N.instMod d)

/-- Type of graded `k`-linear equivalences in degree `d` between two graded modules `M`, `N`. -/
abbrev GrLinEquiv (M N : GradedModuleData.{u, u} k n) (d : ℤ) : Type u :=
  @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k)
    ⟨RingHom.id_comp _, RingHom.comp_id _⟩ ⟨RingHom.id_comp _, RingHom.comp_id _⟩
    (M.component d) (N.component d)
    (M.instACG d).toAddCommMonoid (N.instACG d).toAddCommMonoid (M.instMod d) (N.instMod d)

end MvPolynomialSmooth
end
