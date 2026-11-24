module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Order.Cofinal
public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section35.Part2
open Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-- The additive group structure on `CechCohom X K p`, inherited from the
underlying module. -/
noncomputable instance CechCohomology.CechCohom.addCommGroup
    (X : Type) [TopologicalSpace X]
    (K : Set X) (p : ℕ) : AddCommGroup (CechCohomology.CechCohom X K p) :=
  (CechCohomology.cechCohomology ℤ K p).isAddCommGroup


