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
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section35.Part2
open Set


namespace CechCohomology

open TopologicalSpace SingularCohomology CategoryTheory

variable {X : Type} [TopologicalSpace X]

/-- Continuous inclusion $V \hookrightarrow U$ associated to a relative
neighborhood pair `(U, V)`, viewed as a morphism in `TopCat`. -/
def relNbhdInclusion {K L : Set X} (pair : RelNbhdPair K L) :
    TopCat.of ↑pair.V.1 ⟶ TopCat.of ↑pair.U.1 :=
  ⟨fun x => ⟨x.1, pair.hVU x.2⟩, continuous_inclusion pair.hVU⟩

/-- Relative singular cohomology $H^p(U, V; \mathbb{Z})$ of the pair of open
sets `(U, V)` associated to a relative neighborhood pair. -/
noncomputable def relSingCohomOfPair {K L : Set X}
    (pair : RelNbhdPair K L) (p : ℕ) : ModuleCat.{0} ℤ :=
  relativeSingularCohomology ℤ (TopCat.of ↑pair.U.1) (TopCat.of ↑pair.V.1)
    (relNbhdInclusion pair) (ModuleCat.of ℤ ℤ) p

/-- Index-wise family $\mathrm{pair} \mapsto H^p(U_{\mathrm{pair}}, V_{\mathrm{pair}})$
whose direct limit will define relative Čech cohomology. -/
def relCechFam (K L : Set X) (p : ℕ) (pair : RelNbhdPair K L) : Type :=
  (relSingCohomOfPair pair p : Type _)

end CechCohomology
