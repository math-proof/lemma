/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ForestAcyclicityClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.FacPairwiseClose
import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.RootedTreeSelectorClose
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestColouringClose2.Part3
import Def.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem rfp_not_rootedPrivateArm_of_clawArmGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : rfp_ClawArmGeometry ω n) :
    ¬ fcc_RootedPrivateArm ω n := by
  rintro ⟨b, rank, hbdata, hrank, hpair⟩
  obtain ⟨x₀, hx0box, htri0, harm⟩ := hgeo
  
  have hbx0inf : (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite :=
    (hbdata x₀ hx0box htri0).2.2
  
  obtain ⟨z, hzbox, htriz, hne, hconn, hbeyond, hcrossed⟩ := harm b hbx0inf
  
  have hrk : rank x₀ ≠ rank z := hrank x₀ hx0box htri0 z hzbox htriz hne hconn
  exact rfp_root_arm_obstruction ω n hx0box htri0 hzbox htriz hne hconn hrk hpair
    hbeyond hcrossed


theorem rfp_clawArmGeometry_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hcross : ∀ b : Site d → Site d,
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite →
      ∃ i, Connected d (removeSite x₀ ω) (b x₀) (y i) ∧
        ¬ Connected d (removeSite (y i) ω) (b x₀) x₀) :
    rfp_ClawArmGeometry ω n := by
  refine ⟨x₀, hx0box, htri0, ?_⟩
  intro b hbinf
  obtain ⟨i, hbeyond, hcrossed⟩ := hcross b hbinf
  exact ⟨y i, (hydata i).1, (hydata i).2.1, (hydata i).2.2.1, (hydata i).2.2.2,
    hbeyond, hcrossed⟩


theorem rfp_rootedPrivateArm_refutable (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : rfp_ClawArmGeometry ω n) :
    ¬ fcc_RootedPrivateArm ω n :=
  rfp_not_rootedPrivateArm_of_clawArmGeometry ω n hgeo


end Percolation
end StatMech
