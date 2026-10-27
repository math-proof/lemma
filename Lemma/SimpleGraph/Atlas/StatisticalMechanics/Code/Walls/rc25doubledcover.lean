import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc25doubledcover.Part3
open Finset StatMech StatMech.Walls


/--
[rc25_boxDownUp_strictDecrease](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean)
-/
@[path]
private lemma rc25_boxDownUp_strictDecrease_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox (Down.compression 0 ({∅, {0}, {1}, {2}, {0,1}, {0,2}} : Finset (Finset (Fin 3)))) (rc22_upComp 0 ({∅, {0}, {2}, {0,1}} : Finset (Finset (Fin 3))))) < #(rc20_famCylBox ({∅, {0}, {1}, {2}, {0,1}, {0,2}} : Finset (Finset (Fin 3))) ({∅, {0}, {2}, {0,1}})) := by
-- proof
  apply StatMech.Walls.rc25_boxDownUp_strictDecrease

/--
[rc25_boxDownUpMono_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean)
-/
@[path]
private lemma rc25_boxDownUpMono_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ rc24_BoxDownUpMono := by
-- proof
  apply StatMech.Walls.rc25_boxDownUpMono_false

/--
[rc25_box_le_dpairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean)
-/
@[path]
private lemma rc25_box_le_dpairs_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc25_box_le_dpairs 𝒜 ℬ

/--
[rc25_witness_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean)
-/
@[path]
private lemma rc25_witness_partition_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  (S ∩ rc25_witness 𝒜 ℬ S) ∪ (S ∩ (rc25_witness 𝒜 ℬ S)ᶜ) = S := by
-- proof
  apply StatMech.Walls.rc25_witness_partition 𝒜 ℬ S

/--
[rc25_boxDoubledCount_iff_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean)
-/
@[path]
private lemma rc25_boxDoubledCount_iff_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc25_BoxDoubledCount ↔ rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc25_boxDoubledCount_iff_famCylBoxResidue

/--
[rc25_cylBoxReflInter_of_boxDoubledCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean)
-/
@[path]
private lemma rc25_cylBoxReflInter_of_boxDoubledCount_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc25_BoxDoubledCount) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc25_cylBoxReflInter_of_boxDoubledCount h

/--
[rc25_boxDoubledCount_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean)
-/
@[path]
private lemma rc25_boxDoubledCount_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc22_complPairs 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc25_boxDoubledCount_fin2 𝒜 ℬ

/--
[rc25_boxDoubledCount_strict_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean)
-/
@[path]
private lemma rc25_boxDoubledCount_strict_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3))) ({∅, {0}, {1}, {2}, {0,2}, {1,2}})) < #(rc22_complPairs ({∅, {0}, {1}} : Finset (Finset (Fin 3))) ({∅, {0}, {1}, {2}, {0,2}, {1,2}})) := by
-- proof
  apply StatMech.Walls.rc25_boxDoubledCount_strict_witness

/--
[rc25_reimer_doubledcover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean)
-/
@[path]
private lemma rc25_reimer_doubledcover_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (¬ rc24_BoxDownUpMono) ∧ (∀ (𝒜 ℬ : Finset (Finset α)), #(rc20_famCylBox 𝒜 ℬ) ≤ dpairsCount 𝒜 ℬ) ∧ (∀ (𝒜 ℬ : Finset (Finset α)) (S : Finset α), (S ∩ rc25_witness 𝒜 ℬ S) ∪ (S ∩ (rc25_witness 𝒜 ℬ S)ᶜ) = S) ∧ (rc25_BoxDoubledCount ↔ rc20_FamCylBoxResidue) ∧ (rc25_BoxDoubledCount → rc18_CylBoxReflInter) := by
-- proof
  apply StatMech.Walls.rc25_reimer_doubledcover


-- created on 2026-10-23
