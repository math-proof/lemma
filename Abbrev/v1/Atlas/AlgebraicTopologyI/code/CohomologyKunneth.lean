/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CohomologyKunneth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section29
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section25
import Def.v1.Atlas.AlgebraicTopologyI.code.Section29.Part7
import Def.v1.Atlas.AlgebraicTopologyI.code.Section25.Part3
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Basis.Prod
open CategoryTheory AlgebraicTopology Limits SingularCohomology


noncomputable section

open scoped TensorProduct

namespace CohomologyKunneth

/-- Total singular cohomology of `X` with coefficients in `R`, assembled as the
direct sum `⨁_{n : ℕ} H^n(X; R)` over natural-number degrees. -/
abbrev totalSingularCohomology
    (R : Type) [CommRing R] (X : TopCat.{0}) : Type :=
  DirectSum ℕ (singularCohomologyFamily R X)


end CohomologyKunneth
end
