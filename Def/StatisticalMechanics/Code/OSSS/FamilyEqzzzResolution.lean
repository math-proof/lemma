/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FamilyEqzzzResolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FrontierFamilyClose
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalOSSS
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
open scoped BigOperators
open MeasureTheory Filter Topology

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace FamilyEqzzzResolution

open FrontierFamilyClose LindebergTree Lindeberg

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.MonotonicFK

variable {E : Type*} [Fintype E] [DecidableEq E]


def BareAdaptiveFamilyOSSS {μ : ConfigSpace E → ℝ} {κ : Type*}
    (Tf : κ → DecisionTree E) (f : ConfigSpace E → ℝ) : Prop :=
  ∀ k, Lindeberg.var μ f ≤
    ∑ e, revealmentMu μ (Tf k) e * Lindeberg.cov μ f (Lindeberg.coord e)


def AdaptiveFamilyOSSS {μ : ConfigSpace E → ℝ} {κ : Type*}
    (Tf : κ → DecisionTree E) (f : ConfigSpace E → ℝ) : Prop :=
  (∀ k, (Tf k).evalR = f) ∧ BareAdaptiveFamilyOSSS (μ := μ) Tf f


end FamilyEqzzzResolution
end OSSS
end StatMech
