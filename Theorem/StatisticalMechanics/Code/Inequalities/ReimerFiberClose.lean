/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Def.StatisticalMechanics.Code.Inequalities.ReimerFiberClose
open MeasureTheory Finset
open scoped NNReal BigOperators


namespace StatMech

open ConfigSpace

variable {E : Type*}


lemma DeterminedBy.mono {A : Set (ConfigSpace E)} {K K' : Set E} (hKK' : K ⊆ K')
    (h : DeterminedBy A K) : DeterminedBy A K' :=
  fun ω ω' hω' => h ω ω' (agreeOn_mono hKK' hω')


lemma determinedBy_occursOn {A : Set (ConfigSpace E)} {K : Set E}
    (h : DeterminedBy A K) {ω : ConfigSpace E} (hω : ω ∈ A) : OccursOn A K ω :=
  fun ω' hω' => (h ω ω' hω').mp hω


theorem disjointOccurrence_eq_inter_of_determined {A B : Set (ConfigSpace E)} {K L : Set E}
    (hKL : Disjoint K L) (hA : DeterminedBy A K) (hB : DeterminedBy B L) :
    disjointOccurrence A B = A ∩ B := by
  refine Set.Subset.antisymm (disjointOccurrence_subset_inter A B) ?_
  rintro ω ⟨hωA, hωB⟩
  exact ⟨K, L, hKL, determinedBy_occursOn hA hωA, determinedBy_occursOn hB hωB⟩


section Fintype

variable [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in

lemma restP_symm (p : E → Prop) [DecidablePred p]
    (a : {x // p x} → Bool) (b : {x // ¬ p x} → Bool) :
    (fun x : {x // p x} =>
      (Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (a, b) x.1) = a := by
  funext x; simp only [Equiv.piEquivPiSubtypeProd]; exact dif_pos x.2

omit [Fintype E] [DecidableEq E] in


lemma restNP_symm (p : E → Prop) [DecidablePred p]
    (a : {x // p x} → Bool) (b : {x // ¬ p x} → Bool) :
    (fun x : {x // ¬ p x} =>
      (Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (a, b) x.1) = b := by
  funext x; simp only [Equiv.piEquivPiSubtypeProd]; exact dif_neg x.2


end Fintype
end StatMech
