import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bependpoint
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bep_threeMeetBox_subset_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bependpoint.lean)
-/
@[path]
private lemma bep_threeMeetBox_subset_top_eq
  {n : ℕ} :
-- imply
  threeMeetBox 2 n ⊆ {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} := by
-- proof
  apply StatMech.Walls.bep_threeMeetBox_subset_top n

/--
[bep_hroute_of_encounter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bependpoint.lean)
-/
@[path]
private lemma bep_hroute_of_encounter_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (henc : bep_encounter p hp1) :
-- imply
  ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) → ∃ a₁ a₂ a₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bep_hroute_of_encounter p hp1 henc

/--
[bep_encounter_of_hroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bependpoint.lean)
-/
@[path]
private lemma bep_encounter_of_hroute_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hroute : ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) → ∃ a₁ a₂ a₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (NeighborTrifPrecursor 2 a₁ a₂ a₃)) :
-- imply
  bep_encounter p hp1 := by
-- proof
  apply StatMech.Walls.bep_encounter_of_hroute p hp1 hroute

/--
[bep_encounter_iff_hroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bependpoint.lean)
-/
@[path]
private lemma bep_encounter_iff_hroute_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1) :
-- imply
  bep_encounter p hp1 ↔ (∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) → ∃ a₁ a₂ a₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (NeighborTrifPrecursor 2 a₁ a₂ a₃)) := by
-- proof
  apply StatMech.Walls.bep_encounter_iff_hroute p hp1

/--
[bep_bk_of_encounter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bependpoint.lean)
-/
@[path]
private lemma bep_bk_of_encounter_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (henc : bep_encounter p hp1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bep_bk_of_encounter p hp1 hp0 henc

/--
[bep_bk_atLeastTwo_of_encounter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bependpoint.lean)
-/
@[path]
private lemma bep_bk_atLeastTwo_of_encounter_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (henc : bep_encounter p hp1) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bep_bk_atLeastTwo_of_encounter p hp1 hp0 henc


-- created on 2026-10-23
