/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohAffineEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Def.v1.Atlas.AlgebraicGeometryI.code.QCohAffineEquivalence
open CategoryTheory AlgebraicGeometry


noncomputable section

universe u

namespace Proposition18

/-- `tildeFunctorToQcoh R` is full: every map between tilde sheaves comes from
a module map, lifted from fullness of the underlying tilde functor. -/
instance tildeFunctorToQcoh_full (R : CommRingCat.{u}) : (tildeFunctorToQcoh R).Full where
  map_surjective {M N} f := by
    refine ⟨(tilde.functor R).preimage f.hom, ?_⟩
    apply ObjectProperty.hom_ext
    exact (tilde.functor R).map_preimage f.hom

/-- `tildeFunctorToQcoh R` is faithful: two `R`-module maps with equal tilde
images coincide. -/
instance tildeFunctorToQcoh_faithful (R : CommRingCat.{u}) :
    (tildeFunctorToQcoh R).Faithful where
  map_injective {M N f g} h := by
    have := congr_arg InducedCategory.Hom.hom h
    dsimp [tildeFunctorToQcoh] at this
    exact (tilde.functor R).map_injective this

end Proposition18
end
