/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part2


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFormalRoot
    (L : ℕ) [NeZero L] (omega u v : ℂ) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  PowerSeries.subst (ons_decFormalLog L omega u v)
    (PowerSeries.exp ℂ)

noncomputable def ons_finsetExponent
    {E : Type*} [DecidableEq E] (S : Finset E) : E →₀ ℕ :=
  ∑ edge ∈ S, Finsupp.single edge 1

end StatMech.Onsager
