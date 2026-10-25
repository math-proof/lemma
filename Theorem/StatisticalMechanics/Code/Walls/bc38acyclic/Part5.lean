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
import Def.StatisticalMechanics.Code.Walls.bc38acyclic.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc38_parentFunneling_of_residues (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hspan : bc38_ArmAdjSpanning ω n) (hreal : bc38_ArmRealisation ω n) :
    bc37_ParentFunneling ω n := by
  obtain ⟨rank, par, hinj, hroot⟩ := bc38_exists_rootedArmForest ω n hspan
  obtain ⟨b, hdata, hclauses⟩ := hreal rank par hroot
  exact ⟨b, rank, par, hdata, hinj, hclauses⟩


theorem bc38_selfDownArm_of_residues (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hspan : bc38_ArmAdjSpanning ω n) (hreal : bc38_ArmRealisation ω n) :
    bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n (bc38_parentFunneling_of_residues ω n hspan hreal)


theorem bc38_Tcount_le_boundary_of_residues (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hspan : bc38_ArmAdjSpanning ω n) (hreal : bc38_ArmRealisation ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn (bc38_selfDownArm_of_residues ω n hspan hreal)


theorem bc38_burton_keane_bernoulli_of_residues (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hspan : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc38_ArmAdjSpanning ω n)
    (hreal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc38_ArmRealisation ω n)
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
    (fun ω n hn => bc38_selfDownArm_of_residues ω n (hspan ω n hn) (hreal ω n hn)) htrif


theorem bc38_armAdjSpanning_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc38_ArmAdjSpanning ω n := by
  intro a _b _hconn
  exact absurd (tfc_mem_trifFinset.mp a.2).2 (hno a.1 (tfc_mem_trifFinset.mp a.2).1)

set_option linter.unusedVariables false in


theorem bc38_armAdjSpanning_of_threePath (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ tfc_trifFinset ω n → x = x₀ ∨ x = m ∨ x = g)
    (hx0T : x₀ ∈ tfc_trifFinset ω n) (hmT : m ∈ tfc_trifFinset ω n) (hgT : g ∈ tfc_trifFinset ω n)
    (hadj_x0m : bc37_ArmAdjacent ω n x₀ m) (hadj_mg : bc37_ArmAdjacent ω n m g) :
    bc38_ArmAdjSpanning ω n := by
  classical
  set G := bc37_armAdjGraph ω n with hG
  have exm : G.Adj ⟨x₀, hx0T⟩ ⟨m, hmT⟩ := hadj_x0m
  have emg : G.Adj ⟨m, hmT⟩ ⟨g, hgT⟩ := hadj_mg
  have rx0m : G.Reachable ⟨x₀, hx0T⟩ ⟨m, hmT⟩ := exm.reachable
  have rmg : G.Reachable ⟨m, hmT⟩ ⟨g, hgT⟩ := emg.reachable
  have rx0g : G.Reachable ⟨x₀, hx0T⟩ ⟨g, hgT⟩ := rx0m.trans rmg
  
  have hbase : ∀ (v : {x : Site d // x ∈ tfc_trifFinset ω n}), G.Reachable ⟨x₀, hx0T⟩ v := by
    intro v
    rcases hthree v.1 v.2 with h | h | h
    · rw [show v = ⟨x₀, hx0T⟩ from Subtype.ext h]
    · rw [show v = ⟨m, hmT⟩ from Subtype.ext h]; exact rx0m
    · rw [show v = ⟨g, hgT⟩ from Subtype.ext h]; exact rx0g
  intro a b _hconn
  exact (hbase a).symm.trans (hbase b)


end StatMech.Walls
