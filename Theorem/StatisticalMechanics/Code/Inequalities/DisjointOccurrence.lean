/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/DisjointOccurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Inequalities.DisjointOccurrence


namespace StatMech

open ConfigSpace

variable {E : Type*}


@[refl] lemma agreeOn_refl (K : Set E) (ω : ConfigSpace E) : agreeOn K ω ω :=
  fun _ _ => rfl


lemma agreeOn_symm {K : Set E} {ω ω' : ConfigSpace E} (h : agreeOn K ω ω') :
    agreeOn K ω' ω := fun e he => (h e he).symm


lemma agreeOn_trans {K : Set E} {ω ω' ω'' : ConfigSpace E}
    (h : agreeOn K ω ω') (h' : agreeOn K ω' ω'') : agreeOn K ω ω'' :=
  fun e he => (h' e he).trans (h e he)


lemma agreeOn_mono {K K' : Set E} (hKK' : K ⊆ K') {ω ω' : ConfigSpace E}
    (h : agreeOn K' ω ω') : agreeOn K ω ω' := fun e he => h e (hKK' he)


end StatMech
