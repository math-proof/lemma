/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Def.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem stac_not_divergentArmOrder_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : stac_ClawConfig ω n) : ¬ fsp_DivergentArmOrder ω n := by
  classical
  obtain ⟨x₀, y, lx, ly, ⟨hx0box, htri0⟩, hydata, hyinj, hlxf, hlyf, hydown, hGstar⟩ := hclaw
  rintro ⟨b, hbdata, hdiv⟩
  set T := tfc_trifFinset ω n with hT
  
  have hx0T : x₀ ∈ T := tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩
  have hyT : ∀ i, y i ∈ T := fun i =>
    tfc_mem_trifFinset.mpr ⟨(hydata i).1, (hydata i).2.1⟩
  
  obtain ⟨_, hbx0ne, hbx0conn, hbx0inf⟩ := hbdata x₀ hx0box htri0
  
  have hbx0notin : b x₀ ∉ T := stac_infiniteCluster_notMem T ω hbx0inf
  have hbynotin : ∀ i, b (y i) ∉ T := fun i =>
    stac_infiniteCluster_notMem T ω (hbdata (y i) (hydata i).1 (hydata i).2.1).2.2.2
  
  have hne_bx0 : x₀ ≠ b x₀ := fun h => hbx0notin (h ▸ hx0T)
  have hne_x0_byi : ∀ i, x₀ ≠ b (y i) := fun i h => hbynotin i (h ▸ hx0T)
  have hne_yi_byj : ∀ i j, y i ≠ b (y j) := fun i j h => hbynotin j (h ▸ hyT i)
  
  have hx0byi : ∀ i, Connected d ω x₀ (b (y i)) := fun i =>
    (hydata i).2.2.2.trans (hbdata (y i) (hydata i).1 (hydata i).2.1).2.2.1
  have hyi_byi : ∀ i, Connected d ω (y i) (b (y i)) := fun i =>
    (hbdata (y i) (hydata i).1 (hydata i).2.1).2.2.1
  
  have hyi_byj : ∀ i j, Connected d ω (y i) (b (y j)) := fun i j =>
    ((hydata i).2.2.2.symm.trans (hx0byi j))
  
  set cx : Fin 3 := lx (b x₀) with hcx
  set cy : Fin 3 → Fin 3 := fun i => lx (b (y i)) with hcy
  set ayv : Fin 3 → Fin 3 := fun i => ly i (b (y i)) with hayv
  set ayjv : Fin 3 → Fin 3 → Fin 3 := fun i j => ly i (b (y j)) with hayjv
  
  have Gay : ∀ i, ayv i = 0 ↔ cy i ≠ i := fun i =>
    hGstar i (b (y i)) (hx0byi i) (hne_x0_byi i) (hyi_byi i) (hne_yi_byj i i)
  
  have Gayj : ∀ i j, ayjv i j = 0 ↔ cy j ≠ i := fun i j =>
    hGstar i (b (y j)) (hx0byi j) (hne_x0_byi j) (hyi_byj i j) (hne_yi_byj i j)
  
  have Dx0 : ∀ i, cx ≠ cy i := by
    intro i hcoll
    have hsame : fsp_sameArm ω x₀ (b x₀) (b (y i)) :=
      (hlxf (b x₀) (b (y i)) hbx0conn hne_bx0 (hx0byi i) (hne_x0_byi i)).mp hcoll
    exact hdiv x₀ hx0box htri0 (y i) (hydata i).1 (hydata i).2.1
      (hydata i).2.2.1 (hydata i).2.2.2 hsame
  
  have Dyiyj : ∀ i j, j ≠ i → ayv i ≠ ayjv i j := by
    intro i j hji hcoll
    have hyij : y i ≠ y j := fun h => hji (hyinj h).symm
    have hsame : fsp_sameArm ω (y i) (b (y i)) (b (y j)) :=
      (hlyf i (b (y i)) (b (y j)) (hyi_byi i) (hne_yi_byj i i)
        (hyi_byj i j) (hne_yi_byj i j)).mp hcoll
    exact hdiv (y i) (hydata i).1 (hydata i).2.1 (y j) (hydata j).1 (hydata j).2.1
      hyij ((hydata i).2.2.2.symm.trans (hydata j).2.2.2) hsame
  exact stac_claw_unsat cx cy ayv ayjv Gay Gayj Dx0 Dyiyj


theorem stac_claw_excludes_divergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : stac_ClawConfig ω n) (hdiv : fsp_DivergentArmOrder ω n) : False :=
  stac_not_divergentArmOrder_of_claw ω n hclaw hdiv


theorem stac_uniform_divergentArmOrder_false
    (hex : ∃ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n ∧ stac_ClawConfig ω n) :
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_DivergentArmOrder ω n) := by
  obtain ⟨ω, n, hn, hclaw⟩ := hex
  intro huniform
  exact stac_not_divergentArmOrder_of_claw ω n hclaw (huniform ω n hn)

end Percolation
end StatMech
