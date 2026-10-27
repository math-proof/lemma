import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc70butterflymeasure.Part2
open Finset StatMech StatMech.Walls


/--
[rc70_wt_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_wt_half_eq
  {n : ℕ}
  {U : Finset (Fin n ⊕ Fin n)} :
-- imply
  rc70_wt n (1/2) U = (1/2) ^ (2 * n) := by
-- proof
  apply StatMech.Walls.rc70_wt_half U

/--
[rc70_measure_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_measure_half_eq
  {n : ℕ}
  {Fam : Finset (Finset (Fin n ⊕ Fin n))} :
-- imply
  rc70_measure n (1/2) Fam = Fam.card * (1/2) ^ (2 * n) := by
-- proof
  apply StatMech.Walls.rc70_measure_half Fam

/--
[rc70_measure_half_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_measure_half_invariant_eq
  {n : ℕ}
  {i : Fin n}
  {Fam : Finset (Finset (Fin n ⊕ Fin n))} :
-- imply
  rc70_measure n (1/2) (StatMech.doubleCompress i Fam) = rc70_measure n (1/2) Fam := by
-- proof
  apply StatMech.Walls.rc70_measure_half_invariant i Fam

/--
[rc70_witness_compressed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_witness_compressed_eq
  {n : ℕ} :
-- imply
  StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}) = {{Sum.inr 0}} := by
-- proof
  apply StatMech.Walls.rc70_witness_compressed

/--
[rc70_witness_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_witness_start_eq
  {n : ℕ} :
-- imply
  StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅} = {∅} := by
-- proof
  apply StatMech.Walls.rc70_witness_start

/--
[rc70_measure_increases_at_three_quarters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_measure_increases_at_three_quarters_eq
  {n : ℕ} :
-- imply
  rc70_measure 2 (3/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}) = 1/256 ∧ rc70_measure 2 (3/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) = 3/256 := by
-- proof
  apply StatMech.Walls.rc70_measure_increases_at_three_quarters

/--
[rc70_measure_decreases_at_one_quarter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_measure_decreases_at_one_quarter_eq
  {n : ℕ} :
-- imply
  rc70_measure 2 (1/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}) = 81/256 ∧ rc70_measure 2 (1/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) = 27/256 := by
-- proof
  apply StatMech.Walls.rc70_measure_decreases_at_one_quarter

/--
[rc70_weighted_measure_not_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_weighted_measure_not_monotone_eq
  {n : ℕ} :
-- imply
  (rc70_measure 2 (3/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}) < rc70_measure 2 (3/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}))) ∧ (rc70_measure 2 (1/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) < rc70_measure 2 (1/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) := by
-- proof
  apply StatMech.Walls.rc70_weighted_measure_not_monotone

/--
[rc70_boxDoubled_disjPreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_boxDoubled_disjPreserving_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  rc70_DisjPreserving n (StatMech.boxDoubled 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc70_boxDoubled_disjPreserving 𝒜 ℬ

/--
[rc70_doubleCompress_breaks_disjPreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_doubleCompress_breaks_disjPreserving_eq
  {n : ℕ} :
-- imply
  ¬ rc70_DisjPreserving 2 (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})) := by
-- proof
  apply StatMech.Walls.rc70_doubleCompress_breaks_disjPreserving

/--
[rc70_broken_member_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_broken_member_exists_eq
  {n : ℕ} :
-- imply
  ∃ U ∈ StatMech.doubleCompress (0 : Fin 2) (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}), (Sum.inl (0 : Fin 2)) ∈ U ∧ (Sum.inr (0 : Fin 2)) ∈ U := by
-- proof
  apply StatMech.Walls.rc70_broken_member_exists

/--
[rc70_doubleCompress_card_preserved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_doubleCompress_card_preserved_eq
  {n : ℕ} :
-- imply
  (StatMech.doubleCompress (0 : Fin 2) (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})).card = (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}).card := by
-- proof
  apply StatMech.Walls.rc70_doubleCompress_card_preserved

/--
[rc70_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc70_reimerWprobCore_of_boxUnionBound h

/--
[rc70_reimerWprobCore_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_reimerWprobCore_of_residue_eq
  {n : ℕ}
-- given
  (h : rc69_DoubledMeasureResidue) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc70_reimerWprobCore_of_residue h

/--
[rc70_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc70butterflymeasure.lean)
-/
@[path]
private lemma rc70_status_eq
  {n : ℕ} :
-- imply
  (∀ (m : ℕ) (Fam : Finset (Finset (Fin m ⊕ Fin m))), rc70_measure m (1/2) Fam = Fam.card * (1/2) ^ (2 * m)) ∧ (∀ (m : ℕ) (i : Fin m) (Fam : Finset (Finset (Fin m ⊕ Fin m))), rc70_measure m (1/2) (StatMech.doubleCompress i Fam) = rc70_measure m (1/2) Fam) ∧ ((rc70_measure 2 (3/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}) < rc70_measure 2 (3/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}))) ∧ (rc70_measure 2 (1/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) < rc70_measure 2 (1/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}))) ∧ (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), rc70_DisjPreserving m (StatMech.boxDoubled 𝒜 ℬ)) ∧ (¬ rc70_DisjPreserving 2 (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}))) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc70_status


-- created on 2026-10-23
