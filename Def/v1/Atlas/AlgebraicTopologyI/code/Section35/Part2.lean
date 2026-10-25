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
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section35
open Set


namespace CechCohomology

variable {X : Type*} [TopologicalSpace X]

/-- $p$-th integral singular cohomology $H^p(Y; \mathbb{Z})$ of a space `Y`,
computed by dualising `singChain Y` and taking the `p`-th cohomology. -/
def singCohom (Y : TopCat.{0}) (p : ℕ) : ModuleCat.{0} ℤ :=
  ((singChain.obj Y).linearYonedaObj ℤ (ModuleCat.of ℤ ℤ)).homology p

end CechCohomology

/-- Čech cohomology $\check{H}^p(X, K; \mathbb{Z})$ of a subset `K ⊆ X`,
defined as the direct limit (`cechCohomology`) of singular cohomology over
open neighborhoods of `K`. -/
def CechCohomology.CechCohom
    (X : Type) [TopologicalSpace X] (K : Set X) (p : ℕ) : Type :=
  (CechCohomology.cechCohomology ℤ K p : Type)

