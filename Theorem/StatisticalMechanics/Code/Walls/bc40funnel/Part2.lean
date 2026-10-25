/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Def.StatisticalMechanics.Code.Walls.bc40funnel
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc40_armRealisation_of_cutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc40_RootSideComparable ω n rank par) :
    bc38_ArmRealisation ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  intro rank par hroot
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hpadj, _hprank⟩ := hroot x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hloc, hself, hfun⟩ := hclauses y (par y) hybox htriy hpadj
  refine ⟨hloc, hself, fun hxne => ?_⟩
  
  
  have hxy' : x ≠ y := hxy
  have hrs : Connected d (removeSite y ω) x (par y) :=
    hroot_side rank par x hxbox htri y hybox htriy hxy hconn hlt hxne
  exact hfun x hxy' hrs


theorem bc40_parentFunneling_of_cutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc40_RootSideComparable ω n rank par) :
    bc37_ParentFunneling ω n :=
  bc38_parentFunneling_of_residues ω n (bc39_armAdjSpanning ω n)
    (bc40_armRealisation_of_cutGeometryFixed' ω n hgeo hroot_side)


theorem bc40_selfDownArm_of_cutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc40_RootSideComparable ω n rank par) :
    bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n
    (bc40_parentFunneling_of_cutGeometryFixed' ω n hgeo hroot_side)


theorem bc40_Tcount_le_boundary_of_cutGeometryFixed' (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc40_RootSideComparable ω n rank par) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn
    (bc40_selfDownArm_of_cutGeometryFixed' ω n hgeo hroot_side)


theorem bc40_burton_keane_bernoulli_of_cutGeometryFixed' (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc40_RootSideComparable ω n rank par)
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
    (fun ω n hn => bc40_selfDownArm_of_cutGeometryFixed' ω n (hgeo ω n hn) (hroot_side ω n hn)) htrif


theorem bc40_armCutGeometryFixed'_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc40_ArmCutGeometryFixed' ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro t s htbox htri _; exact absurd htri (hno t htbox)


theorem bc40_armCutGeometryFixed'_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    
    (hloc_x : ∀ s, bc37_ArmAdjacent ω n x₀ s → ¬ Connected d (removeSite x₀ ω) (b x₀) (b s))
    (hself_x : ∀ s, bc37_ArmAdjacent ω n x₀ s → ¬ Connected d (removeSite x₀ ω) (b x₀) s)
    (hloc_y : ∀ s, bc37_ArmAdjacent ω n y₀ s → ¬ Connected d (removeSite y₀ ω) (b y₀) (b s))
    (hself_y : ∀ s, bc37_ArmAdjacent ω n y₀ s → ¬ Connected d (removeSite y₀ ω) (b y₀) s)
    
    (hfun_x : ∀ s, bc37_ArmAdjacent ω n x₀ s → ∀ x, x ≠ x₀ →
      Connected d (removeSite x₀ ω) x s → Connected d (removeSite x₀ ω) (b x) s)
    (hfun_y : ∀ s, bc37_ArmAdjacent ω n y₀ s → ∀ x, x ≠ y₀ →
      Connected d (removeSite y₀ ω) x s → Connected d (removeSite y₀ ω) (b x) s) :
    bc40_ArmCutGeometryFixed' ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · intro t s htbox htri hadj
    rcases htwo t htbox htri with rfl | rfl
    · exact ⟨hloc_x s hadj, hself_x s hadj, hfun_x s hadj⟩
    · exact ⟨hloc_y s hadj, hself_y s hadj, hfun_y s hadj⟩

set_option linter.unusedVariables false in


theorem bc40_armCutGeometryFixed'_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
    
    (hloc : ∀ t s, (t = x₀ ∨ t = m ∨ t = g) → bc37_ArmAdjacent ω n t s →
      ¬ Connected d (removeSite t ω) (b t) (b s))
    (hself : ∀ t s, (t = x₀ ∨ t = m ∨ t = g) → bc37_ArmAdjacent ω n t s →
      ¬ Connected d (removeSite t ω) (b t) s)
    
    (hfun : ∀ t s, (t = x₀ ∨ t = m ∨ t = g) → bc37_ArmAdjacent ω n t s → ∀ x, x ≠ t →
      Connected d (removeSite t ω) x s → Connected d (removeSite t ω) (b x) s) :
    bc40_ArmCutGeometryFixed' ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
  · intro t s htbox htri hadj
    have ht3 : t = x₀ ∨ t = m ∨ t = g := hthree t htbox htri
    exact ⟨hloc t s ht3 hadj, hself t s ht3 hadj, hfun t s ht3 hadj⟩


end StatMech.Walls
