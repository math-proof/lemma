/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Algebra.Group.Subgroup.Ker
import Def.v1.Atlas.AlgebraicTopologyI.code.Section36.Part2
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- Transport the additive commutative group structure from `relCohomOfPair`
to its underlying type `relCechFamily`. -/
instance relCechFamily_addCommGroup {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) :
    AddCommGroup (relCechFamily R p pair) :=
  (relCohomOfPair R pair p).isAddCommGroup

/-- Transport the `R`-module structure from `relCohomOfPair` to its underlying
type `relCechFamily`. -/
instance relCechFamily_module {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) :
    Module R (relCechFamily R p pair) :=
  (relCohomOfPair R pair p).isModule

end FullyRelativeCapProduct
end
