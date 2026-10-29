/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
import Def.StatisticalMechanics.Code.Walls.bc41rootside.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc41_rootSideComparableArm_of_rootWardAvoidingWalk (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hwalk : bc41_RootWardAvoidingWalk ω n rank par) :
    bc41_RootSideComparableArm ω n rank par := by
  intro x hxbox htri y hybox htriy hxy hconn hlt hxpar hadj
  obtain ⟨p, hp⟩ := hwalk x hxbox htri y hybox htriy hxy hconn hlt hxpar hadj
  have hconn_cut : Connected d (removeSites {y} ω) x (par y) := by
    apply bc39_connected_removeSites_of_walk_avoids {y} ω p
    intro v hv
    rw [Finset.mem_singleton]
    exact hp v hv
  rwa [daep_removeSites_singleton] at hconn_cut


theorem bc41_burton_keane_bernoulli_of_rootWardAvoidingWalk (hd : 1 ≤ d) (p : NNReal)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
    (hwalk : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc41_RootWardAvoidingWalk ω n rank par)
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
  bc41_burton_keane_bernoulli_of_cutGeometryFixed'_arm hd p hp1 hp0 hgeo
    (fun ω n hn rank par =>
      bc41_rootSideComparableArm_of_rootWardAvoidingWalk ω n rank par (hwalk ω n hn rank par))
    htrif


theorem bc41_rootWardAvoidingWalk_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc41_RootWardAvoidingWalk ω n rank par := by
  intro x hxbox htri; exact absurd htri (hno x hxbox)


theorem bc41_rootSideComparableArm_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc41_RootSideComparableArm ω n rank par :=
  bc41_rootSideComparableArm_of_rootWardAvoidingWalk ω n rank par
    (bc41_rootWardAvoidingWalk_of_noTrif ω n rank par hno)

set_option linter.unusedVariables false in


theorem bc41_rootWardAvoidingWalk_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (rank : Site d → ℕ ×ₗ ℕ)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hx0y0 : x₀ ≠ y₀) :
    bc41_RootWardAvoidingWalk ω n rank (fun _ => x₀) := by
  intro x hxbox htri y hybox htriy hxy hconn hlt hxpar hadj
  
  simp only at hxpar hadj
  
  rcases htwo x hxbox htri with hx | hx
  · 
    exact absurd hx hxpar
  · 
    rcases htwo y hybox htriy with hy | hy
    · 
      rw [hy] at hadj
      exact absurd hadj (bc37_armAdjacent_irrefl ω n x₀)
    · 
      rw [hx, hy] at hxy
      exact absurd rfl hxy


theorem bc41_rootSideComparableArm_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (rank : Site d → ℕ ×ₗ ℕ)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hx0y0 : x₀ ≠ y₀) :
    bc41_RootSideComparableArm ω n rank (fun _ => x₀) :=
  bc41_rootSideComparableArm_of_rootWardAvoidingWalk ω n rank (fun _ => x₀)
    (bc41_rootWardAvoidingWalk_of_twoTrif ω n rank htwo hx0y0)


theorem bc41_cutGeometryFixed'_downArm_guard_vacuous (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s) :
    ∃ b : Site d → Site d, ¬ Connected d (removeSite t ω) (b t) s := by
  obtain ⟨b, _hdata, hclauses⟩ := hgeo
  obtain ⟨_hloc, hself, _hfun⟩ := hclauses t s htbox htri hadj
  
  exact ⟨b, hself⟩


theorem bc41_cutGeometryFixed'_no_downArm_trap (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s) :
    ∃ b : Site d → Site d,
      (∀ x, x ≠ t → Connected d (removeSite t ω) x s → Connected d (removeSite t ω) (b x) s) ∧
      ¬ Connected d (removeSite t ω) (b t) s := by
  obtain ⟨b, _hdata, hclauses⟩ := hgeo
  obtain ⟨_hloc, hself, hfun⟩ := hclauses t s htbox htri hadj
  exact ⟨b, hfun, hself⟩

end StatMech.Walls
