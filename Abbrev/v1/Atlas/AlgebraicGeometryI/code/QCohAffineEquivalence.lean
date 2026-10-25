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
open CategoryTheory AlgebraicGeometry


noncomputable section

universe u

namespace Proposition18

/-- The category of quasi-coherent sheaves of modules on a scheme `X`, realized
as the full subcategory of `X.Modules` cut out by the quasi-coherence property. -/
abbrev Scheme.Qcoh (X : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory

end Proposition18
end
