/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part2


namespace StatMech

open ConfigSpace

variable {E : Type*}


lemma OccursOn.mem_self {A : Set (ConfigSpace E)} {K : Set E} {ω : ConfigSpace E}
    (h : OccursOn A K ω) : ω ∈ A := h ω (agreeOn_refl K ω)


lemma OccursOn.mono {A : Set (ConfigSpace E)} {K K' : Set E} {ω : ConfigSpace E}
    (h : OccursOn A K ω) (hKK' : K ⊆ K') : OccursOn A K' ω :=
  fun ω' hω' => h ω' (agreeOn_mono hKK' hω')


lemma OccursOn.mono_event {A B : Set (ConfigSpace E)} {K : Set E}
    {ω : ConfigSpace E} (h : OccursOn A K ω) (hAB : A ⊆ B) : OccursOn B K ω :=
  fun ω' hω' => hAB (h ω' hω')


end StatMech
