import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bcl2close
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bcl2_threeMeetBox_subset_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcl2close.lean)
-/
@[path]
private lemma bcl2_threeMeetBox_subset_top_eq
  {n : ℕ} :
-- imply
  threeMeetBox 2 n ⊆ {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} := by
-- proof
  apply StatMech.Walls.bcl2_threeMeetBox_subset_top n

/--
[bcl2_tripleEvent_pos_of_threeMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcl2close.lean)
-/
@[path]
private lemma bcl2_tripleEvent_pos_of_threeMeetBox_eq
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
-- imply
  ∃ (m : ℕ) (x y z : Site 2), 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bxp_tripleEvent 2 m x y z) := by
-- proof
  apply StatMech.Walls.bcl2_tripleEvent_pos_of_threeMeetBox p hp1 n hpos

/--
[bcl2_hroute_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcl2close.lean)
-/
@[path]
private lemma bcl2_hroute_of_bridge_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hbridge : bcl2_Bridge p hp1) :
-- imply
  ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) → ∃ a₁ a₂ a₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bcl2_hroute_of_bridge p hp1 hp0 hplt hbridge

/--
[bcl2_bk_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcl2close.lean)
-/
@[path]
private lemma bcl2_bk_of_bridge_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hbridge : bcl2_Bridge p hp1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bcl2_bk_of_bridge p hp1 hp0 hplt hbridge

/--
[bcl2_bk_atLeastTwo_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcl2close.lean)
-/
@[path]
private lemma bcl2_bk_atLeastTwo_of_bridge_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hbridge : bcl2_Bridge p hp1) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bcl2_bk_atLeastTwo_of_bridge p hp1 hp0 hplt hbridge


-- created on 2026-10-23
