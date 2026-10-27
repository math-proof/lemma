import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
open Finset MeasureTheory StatMech


/--
[isDownAt_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma isDownAt_of_isLowerSet_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {i : α}
-- given
  (h : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  IsDownAt i 𝒜 := by
-- proof
  apply StatMech.isDownAt_of_isLowerSet h i

/--
[isLowerSet_iff_isDownAt_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma isLowerSet_iff_isDownAt_all_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  IsLowerSet (𝒜 : Set (Finset α)) ↔ ∀ i, IsDownAt i 𝒜 := by
-- proof
  apply StatMech.isLowerSet_iff_isDownAt_all 𝒜

/--
[mem_familyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma mem_familyEvent_eq
  [DecidableEq α]
  [Fintype α]
  {𝒜 : Finset (Finset α)}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ familyEvent 𝒜 ↔ cfgSupport ω ∈ 𝒜 := by
-- proof
  apply StatMech.mem_familyEvent

/--
[fwt_eq_pweight_supportCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma fwt_eq_pweight_supportCfg_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {S : Finset α} :
-- imply
  fwt w S = pweight w (supportCfg S) := by
-- proof
  apply StatMech.fwt_eq_pweight_supportCfg w S

/--
[fmarg_eq_wprob_familyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma fmarg_eq_wprob_familyEvent_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 : Finset (Finset α)} :
-- imply
  fmarg w 𝒜 = wprob w (familyEvent 𝒜) := by
-- proof
  apply StatMech.fmarg_eq_wprob_familyEvent w 𝒜

/--
[cfgSupport_subset_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma cfgSupport_subset_of_le_eq
  [DecidableEq α]
  [Fintype α]
  {ω ω' : ConfigSpace α}
-- given
  (h : ω' ≤ ω) :
-- imply
  cfgSupport ω' ⊆ cfgSupport ω := by
-- proof
  apply StatMech.cfgSupport_subset_of_le h

/--
[isDecreasing_familyEvent_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma isDecreasing_familyEvent_of_isLowerSet_eq
  [DecidableEq α]
  [Fintype α]
  {𝒜 : Finset (Finset α)}
-- given
  (h : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  IsDecreasing (familyEvent 𝒜) := by
-- proof
  apply StatMech.isDecreasing_familyEvent_of_isLowerSet h

/--
[isIncreasing_familyEvent_of_isUpperSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma isIncreasing_familyEvent_of_isUpperSet_eq
  [DecidableEq α]
  [Fintype α]
  {𝒜 : Finset (Finset α)}
-- given
  (h : IsUpperSet (𝒜 : Set (Finset α))) :
-- imply
  IsIncreasing (familyEvent 𝒜) := by
-- proof
  apply StatMech.isIncreasing_familyEvent_of_isUpperSet h

/--
[reimer_wprob_familyEvent_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma reimer_wprob_familyEvent_of_isLowerSet_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hw1 : ∀ x, w x false + w x true = 1)
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
-- imply
  wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ)) ≤ wprob w (familyEvent 𝒜) * wprob w (familyEvent ℬ) := by
-- proof
  apply StatMech.reimer_wprob_familyEvent_of_isLowerSet w hw0 hw1 h𝒜 hℬ

/--
[reimer_fmarg_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma reimer_fmarg_of_isLowerSet_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hw1 : ∀ x, w x false + w x true = 1)
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
-- imply
  wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ)) ≤ fmarg w 𝒜 * fmarg w ℬ := by
-- proof
  apply StatMech.reimer_fmarg_of_isLowerSet w hw0 hw1 h𝒜 hℬ

/--
[reimer_wprob_familyEvent_of_isUpperSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma reimer_wprob_familyEvent_of_isUpperSet_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hw1 : ∀ x, w x false + w x true = 1)
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ)) ≤ wprob w (familyEvent 𝒜) * wprob w (familyEvent ℬ) := by
-- proof
  apply StatMech.reimer_wprob_familyEvent_of_isUpperSet w hw0 hw1 h𝒜 hℬ

/--
[isLowerSet_powerset_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma isLowerSet_powerset_univ_eq
  [DecidableEq α]
  [Fintype α] :
-- imply
  IsLowerSet ((Finset.univ.powerset : Finset (Finset α)) : Set (Finset α)) := by
-- proof
  apply StatMech.isLowerSet_powerset_univ

/--
[isLowerSet_principal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma isLowerSet_principal_eq
  [DecidableEq α]
  [Fintype α]
  {S : Finset α} :
-- imply
  IsLowerSet ((Finset.univ.powerset.filter (· ⊆ S)) : Set (Finset α)) := by
-- proof
  apply StatMech.isLowerSet_principal S

/--
[reimer_fmarg_iterDownComp_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean)
-/
@[path]
private lemma reimer_fmarg_iterDownComp_of_isLowerSet_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {cs ds : List α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw0 : ∀ x b, 0 ≤ w x b)
  (hw1 : ∀ x, w x false + w x true = 1)
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
-- imply
  wprob w (disjointOccurrence (familyEvent (iterDownComp cs 𝒜)) (familyEvent (iterDownComp ds ℬ))) ≤ fmarg w (iterDownComp cs 𝒜) * fmarg w (iterDownComp ds ℬ) := by
-- proof
  apply StatMech.reimer_fmarg_iterDownComp_of_isLowerSet w hw0 hw1 cs ds h𝒜 hℬ


-- created on 2026-10-23
