import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Inequalities.ReimerIterationClose
open Finset MeasureTheory StatMech


/--
[rit_familyEvent_powerset_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_familyEvent_powerset_univ_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  familyEvent (Finset.univ.powerset : Finset (Finset (Fin 1))) = (Set.univ : Set (ConfigSpace (Fin 1))) := by
-- proof
  apply StatMech.rit_familyEvent_powerset_univ

/--
[rit_disjointOccurrence_univ_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_disjointOccurrence_univ_univ_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  disjointOccurrence (Set.univ : Set (ConfigSpace (Fin 1))) Set.univ = Set.univ := by
-- proof
  apply StatMech.rit_disjointOccurrence_univ_univ

/--
[rit_wHalf_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_wHalf_prob_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ x, rit_wHalf x false + rit_wHalf x true = 1 := by
-- proof
  apply StatMech.rit_wHalf_prob

/--
[rit_wHalf_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_wHalf_nonneg_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ x b, 0 ≤ rit_wHalf x b := by
-- proof
  apply StatMech.rit_wHalf_nonneg

/--
[rit_collapseLHS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_collapseLHS_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  wprob rit_wHalf (disjointOccurrence (familyEvent (Finset.univ.powerset : Finset (Finset (Fin 1)))) (familyEvent (Finset.univ.powerset))) = 1 := by
-- proof
  apply StatMech.rit_collapseLHS

/--
[rit_collapseRHS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_collapseRHS_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  wdpairs rit_wHalf (Finset.univ.powerset : Finset (Finset (Fin 1))) (Finset.univ.powerset) = 3 / 4 := by
-- proof
  apply StatMech.rit_collapseRHS

/--
[rit_collapseDomination_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_collapseDomination_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β) (w : β → Bool → ℝ), (∀ x b, 0 ≤ w x b) ∧ (∀ x, w x false + w x true = 1) ∧ (∀ x, w x false = w x true) ∧ ∃ 𝒜 ℬ : Finset (Finset β), wdpairs w 𝒜 ℬ < wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ)) := by
-- proof
  apply StatMech.rit_collapseDomination_false

/--
[rit_iterDownComp_append_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_iterDownComp_append_singleton_eq
  [Fintype α]
  [DecidableEq α]
  {cs : List α}
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  iterDownComp (cs ++ [i]) 𝒜 = iterDownComp cs (Down.compression i 𝒜) := by
-- proof
  apply StatMech.rit_iterDownComp_append_singleton cs i 𝒜

/--
[rit_exists_common_iterDownComp_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_exists_common_iterDownComp_isLowerSet_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) ∧ IsLowerSet ((iterDownComp cs ℬ) : Set (Finset α)) := by
-- proof
  apply StatMech.rit_exists_common_iterDownComp_isLowerSet 𝒜 ℬ

/--
[rit_familyEvent_eventFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_familyEvent_eventFamily_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)} :
-- imply
  familyEvent (eventFamily A) = A := by
-- proof
  apply StatMech.rit_familyEvent_eventFamily A

/--
[rit_fmarg_symm_iterDownComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_fmarg_symm_iterDownComp_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {cs : List α}
  {𝒜 : Finset (Finset α)}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  fmarg w (iterDownComp cs 𝒜) = fmarg w 𝒜 := by
-- proof
  apply StatMech.rit_fmarg_symm_iterDownComp hsym cs 𝒜

/--
[rit_boxDownCompMono_eq_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_boxDownCompMono_eq_of_isLowerSet_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
-- imply
  wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ)) = wprob w (disjointOccurrence (familyEvent (Down.compression i 𝒜)) (familyEvent (Down.compression i ℬ))) := by
-- proof
  apply StatMech.rit_boxDownCompMono_eq_of_isLowerSet w i h𝒜 hℬ

/--
[rit_boxDownCompMono_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_boxDownCompMono_fin0_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rit_BoxDownCompMono (Fin 0) := by
-- proof
  apply StatMech.rit_boxDownCompMono_fin0

/--
[rit_box_iterDownComp_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_box_iterDownComp_mono_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {cs : List α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hmono : rit_BoxDownCompMono α)
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hsym : ∀ x, w x false = w x true) :
-- imply
  wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ)) ≤ wprob w (disjointOccurrence (familyEvent (iterDownComp cs 𝒜)) (familyEvent (iterDownComp cs ℬ))) := by
-- proof
  apply StatMech.rit_box_iterDownComp_mono hmono hw0 hsym cs 𝒜 ℬ

/--
[rit_reimer_wprob_symm_of_boxMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_reimer_wprob_symm_of_boxMono_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {A B : Set (ConfigSpace α)}
-- given
  (hmono : rit_BoxDownCompMono α)
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hw1 : ∀ x, w x false + w x true = 1)
  (hsym : ∀ x, w x false = w x true) :
-- imply
  wprob w (disjointOccurrence A B) ≤ wprob w A * wprob w B := by
-- proof
  apply StatMech.rit_reimer_wprob_symm_of_boxMono hmono w hw0 hw1 hsym A B

/--
[rit_reimer_inequality_half_of_boxMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean)
-/
@[path]
private lemma rit_reimer_inequality_half_of_boxMono_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hmono : rit_BoxDownCompMono α) :
-- imply
  (bernoulliProductMeasure (E := α) (1/2) (by norm_num)).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := α) (1/2) (by norm_num)).real A * (bernoulliProductMeasure (E := α) (1/2) (by norm_num)).real B := by
-- proof
  apply StatMech.rit_reimer_inequality_half_of_boxMono hmono A B


-- created on 2026-10-23
