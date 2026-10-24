import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3
open Finset StatMech


/--
[erase_mem_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma erase_mem_of_isLowerSet_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {s : Finset α}
  {i : α}
-- given
  (h : IsLowerSet (𝒜 : Set (Finset α)))
  (hs : s ∈ 𝒜) :
-- imply
  s.erase i ∈ 𝒜 := by
-- proof
  apply StatMech.erase_mem_of_isLowerSet h hs i

/--
[downComp_eq_self_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma downComp_eq_self_of_isLowerSet_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {i : α}
-- given
  (h : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  Down.compression i 𝒜 = 𝒜 := by
-- proof
  apply StatMech.downComp_eq_self_of_isLowerSet h i

/--
[downComp_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma downComp_idem_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  Down.compression i (Down.compression i 𝒜) = Down.compression i 𝒜 := by
-- proof
  apply StatMech.downComp_idem i 𝒜

/--
[iterDownComp_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma iterDownComp_nil_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  iterDownComp [] 𝒜 = 𝒜 := by
-- proof
  apply StatMech.iterDownComp_nil 𝒜

/--
[iterDownComp_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma iterDownComp_cons_eq
  [DecidableEq α]
  {i : α}
  {cs : List α}
  {𝒜 : Finset (Finset α)} :
-- imply
  iterDownComp (i :: cs) 𝒜 = Down.compression i (iterDownComp cs 𝒜) := by
-- proof
  apply StatMech.iterDownComp_cons i cs 𝒜

/--
[iterDownComp_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma iterDownComp_card_eq
  [DecidableEq α]
  {cs : List α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (iterDownComp cs 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.iterDownComp_card cs 𝒜

/--
[dpairsCount_iterDownComp_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma dpairsCount_iterDownComp_mono_eq
  [DecidableEq α]
  {cs : List α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ) := by
-- proof
  apply StatMech.dpairsCount_iterDownComp_mono cs 𝒜 ℬ

/--
[wdpairs_iterDownComp_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma wdpairs_iterDownComp_mono_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {cs : List α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b)
  (hdom : ∀ i ∈ cs, w i true ≤ w i false) :
-- imply
  wdpairs w 𝒜 ℬ ≤ wdpairs w (iterDownComp cs 𝒜) (iterDownComp cs ℬ) := by
-- proof
  apply StatMech.wdpairs_iterDownComp_mono hw cs hdom 𝒜 ℬ

/--
[wdpairs_symm_iterDownComp_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma wdpairs_symm_iterDownComp_mono_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {cs : List α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  wdpairs w 𝒜 ℬ ≤ wdpairs w (iterDownComp cs 𝒜) (iterDownComp cs ℬ) := by
-- proof
  apply StatMech.wdpairs_symm_iterDownComp_mono hsym cs 𝒜 ℬ

/--
[dpairsCount_member_le_nonMember_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma dpairsCount_member_le_nonMember_of_isLowerSet_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
-- imply
  dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.dpairsCount_member_le_nonMember_of_isLowerSet h𝒜 hℬ i

/--
[wdpairs'_member_le_nonMember_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma wdpairs'_member_le_nonMember_of_isLowerSet_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
  {i : α}
-- given
  (hw : ∀ x b, 0 ≤ w x b)
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
-- imply
  wdpairs' w i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.wdpairs'_member_le_nonMember_of_isLowerSet hw h𝒜 hℬ i

/--
[fmarg'_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma fmarg'_mono_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 𝒜' : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b)
  (h : 𝒜 ⊆ 𝒜') :
-- imply
  fmarg' w i 𝒜 ≤ fmarg' w i 𝒜' := by
-- proof
  apply StatMech.fmarg'_mono hw i h

/--
[fmarg'_modular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma fmarg'_modular_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  fmarg' w i (𝒜 ∪ ℬ) + fmarg' w i (𝒜 ∩ ℬ) = fmarg' w i 𝒜 + fmarg' w i ℬ := by
-- proof
  apply StatMech.fmarg'_modular w i 𝒜 ℬ

/--
[fmarg_le_downComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma fmarg_le_downComp_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b)
  (hdom : w i true ≤ w i false) :
-- imply
  fmarg w 𝒜 ≤ fmarg w (Down.compression i 𝒜) := by
-- proof
  apply StatMech.fmarg_le_downComp hw i hdom 𝒜

/--
[fmarg_le_iterDownComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma fmarg_le_iterDownComp_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {cs : List α}
  {𝒜 : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b)
  (hdom : ∀ i ∈ cs, w i true ≤ w i false) :
-- imply
  fmarg w 𝒜 ≤ fmarg w (iterDownComp cs 𝒜) := by
-- proof
  apply StatMech.fmarg_le_iterDownComp hw cs hdom 𝒜

/--
[iterDownComp_eq_self_of_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma iterDownComp_eq_self_of_isLowerSet_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {cs : List α}
-- given
  (h : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  iterDownComp cs 𝒜 = 𝒜 := by
-- proof
  apply StatMech.iterDownComp_eq_self_of_isLowerSet h cs

/--
[downComp_eq_self_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma downComp_eq_self_iff_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  Down.compression i 𝒜 = 𝒜 ↔ ∀ s ∈ 𝒜, s.erase i ∈ 𝒜 := by
-- proof
  apply StatMech.downComp_eq_self_iff i 𝒜

/--
[isLowerSet_of_erase_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma isLowerSet_of_erase_closed_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
-- given
  (h : ∀ s ∈ 𝒜, ∀ i, s.erase i ∈ 𝒜) :
-- imply
  IsLowerSet (𝒜 : Set (Finset α)) := by
-- proof
  apply StatMech.isLowerSet_of_erase_closed h

/--
[isLowerSet_iff_forall_downComp_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma isLowerSet_iff_forall_downComp_eq_self_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  IsLowerSet (𝒜 : Set (Finset α)) ↔ ∀ i, Down.compression i 𝒜 = 𝒜 := by
-- proof
  apply StatMech.isLowerSet_iff_forall_downComp_eq_self 𝒜

/--
[dpairsCount_le_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma dpairsCount_le_endpoint_eq
  [DecidableEq α]
  {cs : List α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)))
  (hℬ : IsLowerSet ((iterDownComp cs ℬ) : Set (Finset α))) :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ) ∧ (∀ i, Down.compression i (iterDownComp cs 𝒜) = iterDownComp cs 𝒜) ∧ (∀ i, Down.compression i (iterDownComp cs ℬ) = iterDownComp cs ℬ) := by
-- proof
  apply StatMech.dpairsCount_le_endpoint cs 𝒜 ℬ h𝒜 hℬ

/--
[wdpairs_le_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma wdpairs_le_endpoint_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {cs : List α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b)
  (hdom : ∀ i ∈ cs, w i true ≤ w i false)
  (h𝒜 : IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)))
  (hℬ : IsLowerSet ((iterDownComp cs ℬ) : Set (Finset α))) :
-- imply
  wdpairs w 𝒜 ℬ ≤ wdpairs w (iterDownComp cs 𝒜) (iterDownComp cs ℬ) ∧ ∀ i, wdpairs' w i ((iterDownComp cs 𝒜).memberSubfamily i) ((iterDownComp cs ℬ).memberSubfamily i) ≤ wdpairs' w i ((iterDownComp cs 𝒜).nonMemberSubfamily i) ((iterDownComp cs ℬ).nonMemberSubfamily i) := by
-- proof
  apply StatMech.wdpairs_le_endpoint hw cs hdom 𝒜 ℬ h𝒜 hℬ

/--
[downComp_eq_image_cmap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma downComp_eq_image_cmap_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  Down.compression i 𝒜 = 𝒜.image (cmap i 𝒜) := by
-- proof
  apply StatMech.downComp_eq_image_cmap i 𝒜

/--
[cmap_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma cmap_injOn_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  Set.InjOn (cmap i 𝒜) (𝒜 : Set (Finset α)) := by
-- proof
  apply StatMech.cmap_injOn i 𝒜

/--
[cmap_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma cmap_card_le_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)}
  {s : Finset α} :
-- imply
  (cmap i 𝒜 s).card ≤ s.card := by
-- proof
  apply StatMech.cmap_card_le i 𝒜 s

/--
[totalSize_downComp_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma totalSize_downComp_le_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  totalSize (Down.compression i 𝒜) ≤ totalSize 𝒜 := by
-- proof
  apply StatMech.totalSize_downComp_le i 𝒜

/--
[totalSize_downComp_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma totalSize_downComp_lt_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)}
-- given
  (hne : Down.compression i 𝒜 ≠ 𝒜) :
-- imply
  totalSize (Down.compression i 𝒜) < totalSize 𝒜 := by
-- proof
  apply StatMech.totalSize_downComp_lt i 𝒜 hne

/--
[exists_iterDownComp_isLowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma exists_iterDownComp_isLowerSet_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) := by
-- proof
  apply StatMech.exists_iterDownComp_isLowerSet 𝒜

/--
[exists_dpairsCount_le_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean)
-/
@[path]
private lemma exists_dpairsCount_le_endpoint_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) ∧ dpairsCount 𝒜 𝒜 ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs 𝒜) := by
-- proof
  apply StatMech.exists_dpairsCount_le_endpoint 𝒜


-- created on 2026-10-23
