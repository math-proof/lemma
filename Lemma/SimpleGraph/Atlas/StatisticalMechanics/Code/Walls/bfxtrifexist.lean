import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bfxtrifexist
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bfx_deleteVertex_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfxtrifexist.lean)
-/
@[path]
private lemma bfx_deleteVertex_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bkg_deleteVertex (openSubgraph d ω) 0 ≤ openSubgraph d (removeSite 0 ω) := by
-- proof
  apply StatMech.Walls.bfx_deleteVertex_le ω

/--
[bfx_fineTrif_of_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfxtrifexist.lean)
-/
@[path]
private lemma bfx_fineTrif_of_classical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc47_IsClassicalTrifurcation ω 0) :
-- imply
  bft_FineTrif ω 0 := by
-- proof
  apply StatMech.Walls.bfx_fineTrif_of_classical ω h

/--
[bfx_coarseSet_eq_fineSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfxtrifexist.lean)
-/
@[path]
private lemma bfx_coarseSet_eq_fineSet_eq
  {d : ℕ} :
-- imply
  {ω : ConfigSpace (Sym2 (Site d)) | bc61_IsCoarseTrifurcation ω 0 0} = {ω | bft_FineTrif ω 0} := by
-- proof
  apply StatMech.Walls.bfx_coarseSet_eq_fineSet

/--
[bfx_trifExistence_of_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfxtrifexist.lean)
-/
@[path]
private lemma bfx_trifExistence_of_route_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hroute : ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) 0 := by
-- proof
  apply StatMech.Walls.bfx_trifExistence_of_route p hp1 hp0 hroute

/--
[bfx_trifExistence_of_routingCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfxtrifexist.lean)
-/
@[path]
private lemma bfx_trifExistence_of_routingCover_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
-- imply
  bc61_CoarseTrifExistence (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1) 0 := by
-- proof
  apply StatMech.Walls.bfx_trifExistence_of_routingCover p hp1 hp0 hrt

/--
[bfx_bk_of_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfxtrifexist.lean)
-/
@[path]
private lemma bfx_bk_of_route_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hroute : ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bfx_bk_of_route hd p hp1 hp0 hroute

/--
[bfx_bk_of_routingCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfxtrifexist.lean)
-/
@[path]
private lemma bfx_bk_of_routingCover_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bfx_bk_of_routingCover hd p hp1 hp0 hrt

/--
[bfx_bk_atLeastTwo_of_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfxtrifexist.lean)
-/
@[path]
private lemma bfx_bk_atLeastTwo_of_route_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hroute : ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 := by
-- proof
  apply StatMech.Walls.bfx_bk_atLeastTwo_of_route hd p hp1 hp0 hroute


-- created on 2026-10-23
