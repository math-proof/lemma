import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bclclose
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bcl_cylinder_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bclclose.lean)
-/
@[path]
private lemma bcl_cylinder_dependsOn_eq
  {I : Finset (Sym2 (Site 2))}
  {η₀ : ConfigSpace ↥I} :
-- imply
  DependsOn (cylinder I ({η₀} : Set (ConfigSpace ↥I))) (↑I : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Walls.bcl_cylinder_dependsOn I η₀

/--
[bcl_cylinder_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bclclose.lean)
-/
@[path]
private lemma bcl_cylinder_measurable_eq
  {I : Finset (Sym2 (Site 2))}
  {η₀ : ConfigSpace ↥I} :
-- imply
  MeasurableSet ((cylinder I ({η₀} : Set (ConfigSpace ↥I))) : Set (ConfigSpace (Sym2 (Site 2)))) := by
-- proof
  apply StatMech.Walls.bcl_cylinder_measurable I η₀

/--
[bcl_hindep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bclclose.lean)
-/
@[path]
private lemma bcl_hindep_eq
  {I : Finset (Sym2 (Site 2))}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site 2}
  {η₀ : ConfigSpace ↥I}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hExtMeas : MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) = bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (cylinder I ({η₀} : Set (ConfigSpace ↥I))) * bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) := by
-- proof
  apply StatMech.Walls.bcl_hindep p hp1 I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hExtMeas

/--
[bcl_precursorPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bclclose.lean)
-/
@[path]
private lemma bcl_precursorPos_eq
  {I : Finset (Sym2 (Site 2))}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site 2}
  {η₀ : ConfigSpace ↥I}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧ (hypercubicLattice 2).Adj 0 a₃)
  (hcorr : ∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)), Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧ Connected 2 (removeSite 0 ω) a₃ x₃)
  (hExtMeas : MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃))
  (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)) :
-- imply
  0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bcl_precursorPos p hp1 hp0 hplt I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hne hadj hcorr hExtMeas hXpos

/--
[bcl_hroute_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bclclose.lean)
-/
@[path]
private lemma bcl_hroute_of_residue_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hres : bcl_ArmResidue p hp1) :
-- imply
  ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) → ∃ a₁ a₂ a₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bcl_hroute_of_residue p hp1 hp0 hplt hres

/--
[bcl_bk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bclclose.lean)
-/
@[path]
private lemma bcl_bk_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hres : bcl_ArmResidue p hp1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | numInfiniteClusters 2 ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bcl_bk p hp1 hp0 hplt hres

/--
[bcl_bk_atLeastTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bclclose.lean)
-/
@[path]
private lemma bcl_bk_atLeastTwo_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hres : bcl_ArmResidue p hp1) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bcl_bk_atLeastTwo p hp1 hp0 hplt hres


-- created on 2026-10-23
