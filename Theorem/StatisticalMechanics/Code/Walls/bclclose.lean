/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bclclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bpt2corridors.Part4
import Theorem.StatisticalMechanics.Code.Walls.bfc2indep
import Theorem.StatisticalMechanics.Code.Walls.bdecdecouple
import Theorem.StatisticalMechanics.Code.Walls.bfxtrifexist
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bcl_cylinder_dependsOn (I : Finset (Sym2 (Site 2))) (η₀ : ConfigSpace ↥I) :
    DependsOn (cylinder I ({η₀} : Set (ConfigSpace ↥I))) (↑I : Set (Sym2 (Site 2))) := by
  intro ω ω' hag
  simp only [MeasureTheory.mem_cylinder, Set.mem_singleton_iff]
  have hres : Finset.restrict I ω = Finset.restrict I ω' := by
    funext i
    exact (hag i.1 (Finset.mem_coe.mpr i.2)).symm
  rw [hres]


theorem bcl_cylinder_measurable (I : Finset (Sym2 (Site 2))) (η₀ : ConfigSpace ↥I) :
    MeasurableSet ((cylinder I ({η₀} : Set (ConfigSpace ↥I))) :
      Set (ConfigSpace (Sym2 (Site 2)))) := by
  have hrestr : Measurable (fun ω : ConfigSpace (Sym2 (Site 2)) => Finset.restrict I ω) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (i : Sym2 (Site 2)))
  exact hrestr (MeasurableSet.of_discrete)


theorem bcl_hindep (p : ℝ≥0) (hp1 : p ≤ 1)
    (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) (η₀ : ConfigSpace ↥I)
    (hExtMeas : MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)
      = bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (cylinder I ({η₀} : Set (ConfigSpace ↥I)))
        * bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) :=
  bfc2_indep_finite_cofinite p hp1 I
    (bcl_cylinder_measurable I η₀) hExtMeas
    (bcl_cylinder_dependsOn I η₀)
    (bpt2_Ext_dependsOn I a₁ a₂ a₃ x₁ x₂ x₃)


theorem bcl_precursorPos (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) (η₀ : ConfigSpace ↥I)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
      (hypercubicLattice 2).Adj 0 a₃)
    (hcorr : ∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
      Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧
        Connected 2 (removeSite 0 ω) a₃ x₃)
    (hExtMeas : MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃))
    (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)) :
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (NeighborTrifPrecursor 2 a₁ a₂ a₃) :=
  bpt2_precursorPos_of_residues p hp1 hp0 hplt I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hne hadj hcorr
    (bcl_hindep p hp1 I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hExtMeas) hXpos


end StatMech.Walls
