/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc35globalarm
import Theorem.StatisticalMechanics.Code.Walls.bc36rooteddiv.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Def.StatisticalMechanics.Code.Walls.bc38acyclic.Part5
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc38_armRealisation_of_cutGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc38_ArmCutGeometry ω n) : bc38_ArmRealisation ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  intro rank par hroot
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hpadj, _hprank⟩ := hroot x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hloc, hself, hfun⟩ := hclauses y (par y) hybox htriy hpadj
  exact ⟨hloc, hself, fun hxne => hfun x hxne⟩


theorem bc38_armCutGeometry_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc38_ArmCutGeometry ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro t s htbox htri _; exact absurd htri (hno t htbox)


theorem bc38_armRealisation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc38_ArmRealisation ω n :=
  bc38_armRealisation_of_cutGeometry ω n (bc38_armCutGeometry_of_noTrif ω n hno)


theorem bc38_cutGeometry_shadow_consistent (parNode bpar bself : ℕ)
    (hnode : parNode ≠ bself) (hbpar : bpar ≠ bself) :
    ∃ up : ℕ → Prop,
      (¬ up bself ∧ up bpar) ∧                          
      (¬ up bself ∧ up parNode) ∧                       
      (∀ w, w ≠ parNode → w ≠ bself → up parNode ∧ up w) := by  
  refine ⟨fun w => w ≠ bself, ⟨by simp, hbpar⟩, ⟨by simp, hnode⟩, ?_⟩
  intro w _hwn hwb
  exact ⟨hnode, hwb⟩


theorem bc38_parentFunneling_of_spanning_cutGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hspan : bc38_ArmAdjSpanning ω n) (hgeo : bc38_ArmCutGeometry ω n) :
    bc37_ParentFunneling ω n :=
  bc38_parentFunneling_of_residues ω n hspan (bc38_armRealisation_of_cutGeometry ω n hgeo)


theorem bc38_selfDownArm_of_spanning_cutGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hspan : bc38_ArmAdjSpanning ω n) (hgeo : bc38_ArmCutGeometry ω n) :
    bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n
    (bc38_parentFunneling_of_spanning_cutGeometry ω n hspan hgeo)


theorem bc38_Tcount_le_boundary_of_spanning_cutGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hspan : bc38_ArmAdjSpanning ω n) (hgeo : bc38_ArmCutGeometry ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn
    (bc38_selfDownArm_of_spanning_cutGeometry ω n hspan hgeo)


theorem bc38_burton_keane_bernoulli_of_spanning_cutGeometry (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hspan : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc38_ArmAdjSpanning ω n)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc38_ArmCutGeometry ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc36_burton_keane_bernoulli_of_selfDownArm hd p hp1 hp0
    (fun ω n hn => bc38_selfDownArm_of_spanning_cutGeometry ω n (hspan ω n hn) (hgeo ω n hn)) htrif

end StatMech.Walls
