import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bdecdecouple
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bdec_forceOpen_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdecdecouple.lean)
-/
@[path]
private lemma bdec_forceOpen_empty_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
-- proof
  apply StatMech.Walls.bdec_forceOpen_empty ω

/--
[bdec_forceOpen_empty_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdecdecouple.lean)
-/
@[path]
private lemma bdec_forceOpen_empty_preimage_eq
  {d : ℕ}
  {A : Set (ConfigSpace (Sym2 (Site d)))} :
-- imply
  (fun ω => forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω) ⁻¹' A = A := by
-- proof
  apply StatMech.Walls.bdec_forceOpen_empty_preimage A

/--
[bdec_posRouting_of_precursorPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdecdecouple.lean)
-/
@[path]
private lemma bdec_posRouting_of_precursorPos_eq
  {d : ℕ}
  {n : ℕ}
  {a₁ a₂ a₃ : Site d}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  brt2_PosRouting (d := d) p hp1 n := by
-- proof
  apply StatMech.Walls.bdec_posRouting_of_precursorPos p hp1 n a₁ a₂ a₃ hpos

/--
[bdec_cylinder_singleton_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdecdecouple.lean)
-/
@[path]
private lemma bdec_cylinder_singleton_pos_eq
  {d : ℕ}
  {I : Finset (Sym2 (Site d))}
  {η₀ : ConfigSpace ↥I}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1) :
-- imply
  0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder I {η₀}) := by
-- proof
  apply StatMech.Walls.bdec_cylinder_singleton_pos p hp1 hp0 hplt I η₀

/--
[bdec_factor_finite_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdecdecouple.lean)
-/
@[path]
private lemma bdec_factor_finite_pos_eq
  {d : ℕ}
  {s t : Finset (Sym2 (Site d))}
  {S : Set (∀ i : s, Bool)}
  {T : Set (∀ i : t, Bool)}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hS : MeasurableSet S)
  (hT : MeasurableSet T)
  (hdisj : Disjoint s t)
  (hSpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder s S))
  (hTpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder t T)) :
-- imply
  0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder s S ∩ cylinder t T) := by
-- proof
  apply StatMech.Walls.bdec_factor_finite_pos p hp1 hS hT hdisj hSpos hTpos

/--
[bdec_precursorPos_of_decoupled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdecdecouple.lean)
-/
@[path]
private lemma bdec_precursorPos_of_decoupled_eq
  {d : ℕ}
  {a₁ a₂ a₃ : Site d}
  {I : Finset (Sym2 (Site d))}
  {η₀ : ConfigSpace ↥I}
  {X : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hindep : bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ X) = bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder I ({η₀} : Set (ConfigSpace ↥I))) * bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 X)
  (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 X)
  (hgeo : cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ X ⊆ NeighborTrifPrecursor d a₁ a₂ a₃) :
-- imply
  0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bdec_precursorPos_of_decoupled p hp1 hp0 hplt a₁ a₂ a₃ I η₀ X hindep hXpos hgeo

/--
[bdec_bk_of_precursorPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdecdecouple.lean)
-/
@[path]
private lemma bdec_bk_of_precursorPos_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hpre : ∀ n : ℕ, ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bdec_bk_of_precursorPos hd p hp1 hp0 hpre

/--
[bdec_bk_atLeastTwo_of_precursorPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bdecdecouple.lean)
-/
@[path]
private lemma bdec_bk_atLeastTwo_of_precursorPos_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hpre : ∀ n : ℕ, ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 := by
-- proof
  apply StatMech.Walls.bdec_bk_atLeastTwo_of_precursorPos hd p hp1 hp0 hpre


-- created on 2026-10-23
