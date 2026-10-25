/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Colimit.Module
import Mathlib.Order.Cofinal
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Def.v1.Atlas.AlgebraicTopologyI.code.Section35.Part7
open Set


/-- Preorder on the LES index type, inherited from `relNbhdPair_preorder`. -/
instance CechCohomology.lesIndexPreorder
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    Preorder (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_preorder

/-- Directedness of the LES index type. -/
instance CechCohomology.lesIndexDirected
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    IsDirectedOrder (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_directed

/-- Classical decidable equality on the LES index type. -/
noncomputable instance CechCohomology.lesIndexDecEq
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    DecidableEq (CechCohomology.lesIndexType X K L) :=
  open Classical in inferInstance

/-- Nonemptiness of the LES index type. -/
instance CechCohomology.lesIndexNonempty
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    Nonempty (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_nonempty

