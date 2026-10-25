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
import Instance.v1.Atlas.AlgebraicGeometryI.code.QCohAffineEquivalence
open CategoryTheory AlgebraicGeometry


noncomputable section

universe u

namespace Proposition18

set_option backward.isDefEq.respectTransparency false in


/-- Converse direction (Thm 12.1): every quasi-coherent sheaf on `Spec R`
arises (up to isomorphism) as `M̃` for some `R`-module `M`. -/
def qcoh_spec_equiv_moduleCat (R : CommRingCat.{u}) :
    ModuleCat.{u} R ≌ Scheme.Qcoh (Spec R) :=
  (tildeFunctorToQcoh R).asEquivalence


end Proposition18
end
