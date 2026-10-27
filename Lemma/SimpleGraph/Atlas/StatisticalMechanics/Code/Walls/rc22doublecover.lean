import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
open Finset StatMech StatMech.Walls


/--
[rc22_mem_complPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_mem_complPairs_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {p : Finset α × Finset α} :
-- imply
  p ∈ rc22_complPairs 𝒜 ℬ ↔ p.1 ∈ 𝒜 ∧ p.2 ∈ ℬ ∧ Disjoint p.1 p.2 ∧ p.1 ∪ p.2 = univ := by
-- proof
  apply StatMech.Walls.rc22_mem_complPairs 𝒜 ℬ p

/--
[rc22_compl_of_disjoint_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_compl_of_disjoint_union_eq
  [Fintype α]
  [DecidableEq α]
  {S T : Finset α}
-- given
  (hd : Disjoint S T)
  (hu : S ∪ T = univ) :
-- imply
  Sᶜ = T := by
-- proof
  apply StatMech.Walls.rc22_compl_of_disjoint_union hd hu

/--
[rc22_card_reflInter_eq_complPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_card_reflInter_eq_complPairs_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter 𝒜 ℬ) = #(rc22_complPairs 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc22_card_reflInter_eq_complPairs 𝒜 ℬ

/--
[rc22_complPairs_eq_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_complPairs_eq_filter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc22_complPairs 𝒜 ℬ = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => p.1 ∪ p.2 = univ) := by
-- proof
  apply StatMech.Walls.rc22_complPairs_eq_filter 𝒜 ℬ

/--
[rc22_reflInter_le_dpairsCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_reflInter_le_dpairsCount_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter 𝒜 ℬ) ≤ dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc22_reflInter_le_dpairsCount 𝒜 ℬ

/--
[rc22_mem_complFam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_mem_complFam_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc22_complFam ℬ ↔ Sᶜ ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc22_mem_complFam ℬ S

/--
[rc22_card_complFam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_card_complFam_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  #(rc22_complFam ℬ) = #ℬ := by
-- proof
  apply StatMech.Walls.rc22_card_complFam ℬ

/--
[rc22_reflInter_eq_inter_complFam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_reflInter_eq_inter_complFam_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc22_complFam ℬ := by
-- proof
  apply StatMech.Walls.rc22_reflInter_eq_inter_complFam 𝒜 ℬ

/--
[rc22_famCylBox_subset_boxSupp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_famCylBox_subset_boxSupp_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ rc10_boxSupp 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc22_famCylBox_subset_boxSupp 𝒜 ℬ

/--
[rc22_famCylBox_le_reflInter_of_upperSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_famCylBox_le_reflInter_of_upperSet_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n))))
  (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc22_famCylBox_le_reflInter_of_upperSet h𝒜 hℬ

/--
[rc22_interCountResidue_iff_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_interCountResidue_iff_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc22_InterCountResidue ↔ rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc22_interCountResidue_iff_famCylBoxResidue

/--
[rc22_cylBoxReflInter_of_interCountResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_cylBoxReflInter_of_interCountResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc22_InterCountResidue) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc22_cylBoxReflInter_of_interCountResidue h

/--
[rc22_fiber_inter_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_fiber_inter_ineq_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {am an cm cn : Finset β} :
-- imply
  #((am ∩ an) ∩ (cm ∪ cn)) + #((am ∪ an) ∩ (cm ∩ cn)) ≤ #(am ∩ cm) + #(an ∩ cn) := by
-- proof
  apply StatMech.Walls.rc22_fiber_inter_ineq am an cm cn

/--
[rc22_uvCompress_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_uvCompress_singleton_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {a : β}
  {s : Finset β} :
-- imply
  UV.compress ({a} : Finset β) ∅ s = insert a s := by
-- proof
  apply StatMech.Walls.rc22_uvCompress_singleton a s

/--
[rc22_mem_upComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_mem_upComp_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {i : β}
  {𝒜 : Finset (Finset β)}
  {s : Finset β} :
-- imply
  s ∈ rc22_upComp i 𝒜 ↔ (s ∈ 𝒜 ∧ insert i s ∈ 𝒜) ∨ (s ∉ 𝒜 ∧ ∃ b ∈ 𝒜, insert i b = s) := by
-- proof
  apply StatMech.Walls.rc22_mem_upComp i 𝒜 s

/--
[rc22_upComp_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_upComp_card_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {i : β}
  {𝒜 : Finset (Finset β)} :
-- imply
  (rc22_upComp i 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc22_upComp_card i 𝒜

/--
[rc22_upComp_nonMemberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_upComp_nonMemberSubfamily_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {i : β}
  {𝒞 : Finset (Finset β)} :
-- imply
  (rc22_upComp i 𝒞).nonMemberSubfamily i = 𝒞.memberSubfamily i ∩ 𝒞.nonMemberSubfamily i := by
-- proof
  apply StatMech.Walls.rc22_upComp_nonMemberSubfamily i 𝒞

/--
[rc22_upComp_memberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_upComp_memberSubfamily_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {i : β}
  {𝒞 : Finset (Finset β)} :
-- imply
  (rc22_upComp i 𝒞).memberSubfamily i = 𝒞.memberSubfamily i ∪ 𝒞.nonMemberSubfamily i := by
-- proof
  apply StatMech.Walls.rc22_upComp_memberSubfamily i 𝒞

/--
[rc22_downInterUp_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_downInterUp_le_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {i : β}
  {𝒜 𝒞 : Finset (Finset β)} :
-- imply
  #(Down.compression i 𝒜 ∩ rc22_upComp i 𝒞) ≤ #(𝒜 ∩ 𝒞) := by
-- proof
  apply StatMech.Walls.rc22_downInterUp_le i 𝒜 𝒞

/--
[rc22_mem_complImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_mem_complImage_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  [Fintype β]
  {ℬ : Finset (Finset β)}
  {s : Finset β} :
-- imply
  s ∈ ℬ.image compl ↔ sᶜ ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc22_mem_complImage ℬ s

/--
[rc22_complImage_downCompression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_complImage_downCompression_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  [Fintype β]
  {i : β}
  {ℬ : Finset (Finset β)} :
-- imply
  (Down.compression i ℬ).image compl = rc22_upComp i (ℬ.image compl) := by
-- proof
  apply StatMech.Walls.rc22_complImage_downCompression i ℬ

/--
[rc22_reflInter_downDown_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_reflInter_downDown_antitone_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  [Fintype β]
  {i : β}
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  #(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ)) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc22_reflInter_downDown_antitone i 𝒜 ℬ

/--
[rc22_reflInter_iterDownComp_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_reflInter_iterDownComp_antitone_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  [Fintype β]
  {cs : List β}
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  #(rc10_reflInter (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc22_reflInter_iterDownComp_antitone cs 𝒜 ℬ

/--
[rc22_traceClosed_iff_of_lowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_traceClosed_iff_of_lowerSet_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {𝒜 : Finset (Finset α)}
  {K S : Finset α}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) :
-- imply
  (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ↔ (S ∪ Kᶜ) ∈ 𝒜 := by
-- proof
  apply StatMech.Walls.rc22_traceClosed_iff_of_lowerSet h𝒜 K S

/--
[rc22_mem_famCylBox_of_lowerSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_mem_famCylBox_of_lowerSet_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
-- imply
  S ∈ rc20_famCylBox 𝒜 ℬ ↔ ∃ K L : Finset α, Disjoint K L ∧ (S ∪ Kᶜ) ∈ 𝒜 ∧ (S ∪ Lᶜ) ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc22_mem_famCylBox_of_lowerSet h𝒜 hℬ S

/--
[rc22_famCylBox_iterDownComp_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_famCylBox_iterDownComp_mono_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {n : ℕ}
  {cs : List (Fin n)}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : rc22_BoxCompressionMono) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc20_famCylBox (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) := by
-- proof
  apply StatMech.Walls.rc22_famCylBox_iterDownComp_mono h cs 𝒜 ℬ

/--
[rc22_famCylBoxResidue_of_boxCompression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_famCylBoxResidue_of_boxCompression_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
-- given
  (hmono : rc22_BoxCompressionMono)
  (hbase : rc22_BoxDownsetBase) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc22_famCylBoxResidue_of_boxCompression hmono hbase

/--
[rc22_cylBoxReflInter_of_boxCompression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_cylBoxReflInter_of_boxCompression_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
-- given
  (hmono : rc22_BoxCompressionMono)
  (hbase : rc22_BoxDownsetBase) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc22_cylBoxReflInter_of_boxCompression hmono hbase

/--
[rc22_boxDownsetBase_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_boxDownsetBase_fin0_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset (Fin 0))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc22_boxDownsetBase_fin0 𝒜 ℬ

/--
[rc22_boxDownsetBase_upperSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_boxDownsetBase_upperSet_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n))))
  (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc22_boxDownsetBase_upperSet h𝒜 hℬ

/--
[rc22_reimer_doublecover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean)
-/
@[path]
private lemma rc22_reimer_doublecover_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset α)), #(rc10_reflInter 𝒜 ℬ) = #(rc22_complPairs 𝒜 ℬ)) ∧ (∀ (𝒜 ℬ : Finset (Finset α)), rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc22_complFam ℬ) ∧ (∀ (𝒜 ℬ : Finset (Finset α)), rc20_famCylBox 𝒜 ℬ ⊆ rc10_boxSupp 𝒜 ℬ) ∧ (rc22_InterCountResidue ↔ rc20_FamCylBoxResidue) ∧ (∀ [Fintype α] (i : α) (𝒜 ℬ : Finset (Finset α)), #(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ)) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc22_BoxCompressionMono → rc22_BoxDownsetBase → rc18_CylBoxReflInter) := by
-- proof
  apply StatMech.Walls.rc22_reimer_doublecover


-- created on 2026-10-23
