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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section36
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- A pair `(U, V)` of open neighbourhoods with `K ⊆ U`, `L ⊆ V` and `V ⊆ U`,
indexing the directed system used to define relative Čech cohomology
`Ȟ^p(K, L; R)`. -/
structure OpenNbhdPair {X : Type} [TopologicalSpace X] (K L : Set X) where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  hK : K ⊆ ↑U
  hL : L ⊆ ↑V
  hVU : V ≤ U

end FullyRelativeCapProduct
end
