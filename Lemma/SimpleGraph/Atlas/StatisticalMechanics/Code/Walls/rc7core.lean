import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc7core.Part4
open Finset StatMech StatMech.Walls


/--
[rc7_reimerCardFormAll_iff_literal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_reimerCardFormAll_iff_literal_eq :
-- imply
  ReimerCardFormAll ↔ ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B)) ≤ #(Finset.univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ A ∧ (fun a => !ω a) ∈ B)) := by
-- proof
  apply StatMech.Walls.rc7_reimerCardFormAll_iff_literal

/--
[rc7_flip_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_flip_apply_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {ω : ConfigSpace α}
  {a : α} :
-- imply
  rc7_flip i ω a = if a = i then !ω a else ω a := by
-- proof
  apply StatMech.Walls.rc7_flip_apply i ω a

/--
[rc7_flip_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_flip_self_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {ω : ConfigSpace α} :
-- imply
  rc7_flip i ω i = !ω i := by
-- proof
  apply StatMech.Walls.rc7_flip_self i ω

/--
[rc7_flip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_flip_involutive_eq
  [Fintype α]
  [DecidableEq α]
  {i : α} :
-- imply
  Function.Involutive (rc7_flip i) := by
-- proof
  apply StatMech.Walls.rc7_flip_involutive i

/--
[rc7_flip_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_flip_injective_eq
  [Fintype α]
  [DecidableEq α]
  {i : α} :
-- imply
  Function.Injective (rc7_flip i) := by
-- proof
  apply StatMech.Walls.rc7_flip_injective i

/--
[rc7_mem_downEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_mem_downEvent_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {A : Set (ConfigSpace α)}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ rc7_downEvent i A ↔ (if ω i = false then (ω ∈ A ∨ rc7_flip i ω ∈ A) else (ω ∈ A ∧ rc7_flip i ω ∈ A)) := by
-- proof
  apply StatMech.Walls.rc7_mem_downEvent i A ω

/--
[rc7_downEvent_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_downEvent_card_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {A : Set (ConfigSpace α)} :
-- imply
  #(univ.filter (fun ω => ω ∈ rc7_downEvent i A)) = #(univ.filter (fun ω => ω ∈ A)) := by
-- proof
  apply StatMech.Walls.rc7_downEvent_card i A

/--
[rc7_downEvent_down_in_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_downEvent_down_in_coord_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {A : Set (ConfigSpace α)}
  {ω : ConfigSpace α}
-- given
  (hω : ω ∈ rc7_downEvent i A)
  (hi : ω i = true) :
-- imply
  rc7_flip i ω ∈ rc7_downEvent i A := by
-- proof
  apply StatMech.Walls.rc7_downEvent_down_in_coord i A hω hi

/--
[rc7_downEvent_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_downEvent_idem_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {A : Set (ConfigSpace α)} :
-- imply
  rc7_downEvent i (rc7_downEvent i A) = rc7_downEvent i A := by
-- proof
  apply StatMech.Walls.rc7_downEvent_idem i A

/--
[rc7_compressionEngine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_compressionEngine_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ) ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ)) ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i)) ∧ (∀ cs : List β, (iterDownComp cs 𝒜).card = 𝒜.card) ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β)) ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β, dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
-- proof
  apply StatMech.Walls.rc7_compressionEngine 𝒜 ℬ

/--
[rc7_reflectionDeficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_reflectionDeficit_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α) ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B)) = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B))) ∧ (StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0) := by
-- proof
  apply StatMech.Walls.rc7_reflectionDeficit A B

/--
[rc7_reindexTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_reindexTransfer_eq
  [Fintype β]
  [DecidableEq β]
  {A B : Set (ConfigSpace β)}
-- given
  (hcard : ReimerCardFormAll) :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc7_reindexTransfer hcard A B

/--
[rc7_deficitBridge_iff_reimerCardFormAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_deficitBridge_iff_reimerCardFormAll_eq :
-- imply
  rc7_DeficitBridge ↔ ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc7_deficitBridge_iff_reimerCardFormAll

/--
[rc7_reimerCardFormAll_of_deficitBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_reimerCardFormAll_of_deficitBridge_eq
-- given
  (h : rc7_DeficitBridge) :
-- imply
  ReimerCardFormAll := by
-- proof
  apply StatMech.Walls.rc7_reimerCardFormAll_of_deficitBridge h

/--
[rc7_naiveBoxCompression_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_naiveBoxCompression_refuted_eq :
-- imply
  ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2), (boxDoubled (Down.compression i 𝒜) (UV.compression ({i} : Finset (Fin 2)) ∅ ℬ)).card < (boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc7_naiveBoxCompression_refuted

/--
[rc7_reimerCardFormAll_iff_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_reimerCardFormAll_iff_residue_eq :
-- imply
  ReimerCardFormAll ↔ ReimerResidue := by
-- proof
  apply StatMech.Walls.rc7_reimerCardFormAll_iff_residue

/--
[rc7_reimer_inequality_of_deficitBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_reimer_inequality_of_deficitBridge_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : rc7_DeficitBridge)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Walls.rc7_reimer_inequality_of_deficitBridge h hp A B

/--
[rc7_deficit_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_deficit_rbi_eq :
-- imply
  rc5_deficit rbi_A rbi_B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc7_deficit_rbi

/--
[rc7_deficit_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_deficit_one_eq
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc7_deficit_one A B

/--
[rc7_cardform_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean)
-/
@[path]
private lemma rc7_cardform_all_eq :
-- imply
  (rc7_DeficitBridge ↔ ReimerCardFormAll) ∧ (rc7_DeficitBridge → ReimerCardFormAll) ∧ (ReimerCardFormAll ↔ ReimerResidue) ∧ (∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2), (boxDoubled (Down.compression i 𝒜) (UV.compression ({i} : Finset (Fin 2)) ∅ ℬ)).card < (boxDoubled 𝒜 ℬ).card) := by
-- proof
  apply StatMech.Walls.rc7_cardform_all


-- created on 2026-10-23
