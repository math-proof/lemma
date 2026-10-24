import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc_core
open Finset StatMech StatMech.Walls


/--
[rc_core_diagonal_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_diagonal_empty_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1 ∧ i ∈ p.2) = ∅ := by
-- proof
  apply StatMech.Walls.rc_core_diagonal_empty 𝒜 ℬ i

/--
[rc_core_fiber_repairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_fiber_repairing_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  dpairsCount 𝒜 ℬ = dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) + dpairsCount (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i) + dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc_core_fiber_repairing 𝒜 ℬ i

/--
[rc_core_deficit_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_deficit_identity_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc_core_deficit_identity 𝒜 ℬ i

/--
[rc_core_box_compress_preserve](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_box_compress_preserve_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) := by
-- proof
  apply StatMech.Walls.rc_core_box_compress_preserve 𝒜 ℬ i

/--
[rc_core_deficit_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_deficit_nonneg_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (0 : ℤ) ≤ (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc_core_deficit_nonneg 𝒜 ℬ i

/--
[rc_core_iter_box_compress_preserve](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_iter_box_compress_preserve_eq
  [DecidableEq α]
  {cs : List α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ) := by
-- proof
  apply StatMech.Walls.rc_core_iter_box_compress_preserve cs 𝒜 ℬ

/--
[rc_core_iter_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_iter_card_eq
  [DecidableEq α]
  {cs : List α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (iterDownComp cs 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc_core_iter_card cs 𝒜

/--
[rc_core_endpoint_favourable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_endpoint_favourable_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
-- imply
  dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc_core_endpoint_favourable h𝒜 hℬ i

/--
[rc_core_exists_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_exists_endpoint_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  ∃ cs : List α, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc_core_exists_endpoint 𝒜

/--
[rc_core_downUp_box_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_downUp_box_refuted_eq
  [DecidableEq α] :
-- imply
  ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2), (boxDoubled (Down.compression i 𝒜) (UV.compression ({i} : Finset (Fin 2)) ∅ ℬ)).card < (boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc_core_downUp_box_refuted

/--
[rc_core_fixed_deficit_le_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_fixed_deficit_le_rbi_eq
  [DecidableEq α] :
-- imply
  poc_ReimerCardForm rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc_core_fixed_deficit_le_rbi

/--
[rc_core_reimerCardForm_iff_deficit_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_reimerCardForm_iff_deficit_le_eq
  [DecidableEq α]
  [Fintype α]
  {A B : Set (ConfigSpace α)} :
-- imply
  StatMech.poc_ReimerCardForm A B ↔ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤ #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
-- proof
  apply StatMech.Walls.rc_core_reimerCardForm_iff_deficit_le A B

/--
[rc_core_countBoxBridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_countBoxBridge_iff_eq
  [DecidableEq α] :
-- imply
  rc_core_CountBoxBridge ↔ StatMech.poc_SlabCardAll := by
-- proof
  apply StatMech.Walls.rc_core_countBoxBridge_iff

/--
[rc_core_reimer_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_reimer_of_bridge_eq
  [DecidableEq α]
-- given
  (h : rc_core_CountBoxBridge) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc_core_reimer_of_bridge h

/--
[rc_core_reimer_inequality_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_reimer_inequality_of_bridge_eq
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc_core_CountBoxBridge)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc_core_reimer_inequality_of_bridge h hp A B

/--
[rc_core_bridge_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_bridge_of_disjoint_support_eq
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace β)}
  {S T : Finset β}
-- given
  (hA : StatMech.DependsOn A (↑S))
  (hB : StatMech.DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rc_core_bridge_of_disjoint_support hA hB hST

/--
[rc_core_bridge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_bridge_one_eq
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rc_core_bridge_one A B

/--
[rc_core_bridge_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean)
-/
@[path]
private lemma rc_core_bridge_of_box_empty_eq
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace β)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.Walls.rc_core_bridge_of_box_empty hbox


-- created on 2026-10-23
