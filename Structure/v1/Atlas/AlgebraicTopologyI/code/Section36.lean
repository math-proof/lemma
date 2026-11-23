/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section36
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


public noncomputable section

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
