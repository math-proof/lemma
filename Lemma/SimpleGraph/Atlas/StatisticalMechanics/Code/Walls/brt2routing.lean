import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.brt2routing
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[brt2_precursor_pos_of_forceOpen_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brt2routing.lean)
-/
@[path]
private lemma brt2_precursor_pos_of_forceOpen_pos_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {G : Finset (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hpos : 0 < μ ((fun ω => forceOpenFinset G ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.brt2_precursor_pos_of_forceOpen_pos μ hfe G a₁ a₂ a₃ hpos

/--
[brt2_route_of_posRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brt2routing.lean)
-/
@[path]
private lemma brt2_route_of_posRouting_eq
  {d : ℕ}
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hpr : ∀ n : ℕ, brt2_PosRouting (d := d) p hp1 n) :
-- imply
  ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.brt2_route_of_posRouting p hp1 hp0 hpr

/--
[brt2_posRouting_of_routingCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brt2routing.lean)
-/
@[path]
private lemma brt2_posRouting_of_routingCover_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hrt : hrHD_DisjointRouting d n) :
-- imply
  brt2_PosRouting (d := d) p hp1 n := by
-- proof
  apply StatMech.Walls.brt2_posRouting_of_routingCover p hp1 hrt

/--
[brt2_bk_of_posRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brt2routing.lean)
-/
@[path]
private lemma brt2_bk_of_posRouting_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hpr : ∀ n : ℕ, brt2_PosRouting (d := d) p hp1 n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.brt2_bk_of_posRouting hd p hp1 hp0 hpr

/--
[brt2_bk_atLeastTwo_of_posRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brt2routing.lean)
-/
@[path]
private lemma brt2_bk_atLeastTwo_of_posRouting_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hpr : ∀ n : ℕ, brt2_PosRouting (d := d) p hp1 n) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 := by
-- proof
  apply StatMech.Walls.brt2_bk_atLeastTwo_of_posRouting hd p hp1 hp0 hpr


-- created on 2026-10-23
