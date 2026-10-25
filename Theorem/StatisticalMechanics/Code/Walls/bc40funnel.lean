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
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc40_funnel_demands_all_sites_reach_s (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc39_ArmCutGeometryFixed ω n)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s) :
    ∃ b : Site d → Site d, ∀ x, x ≠ s → x ≠ t → Connected d (removeSite t ω) (b x) s := by
  obtain ⟨b, _hdata, hclauses⟩ := hgeo
  obtain ⟨_hloc, _hself, hfun⟩ := hclauses t s htbox htri hadj
  exact ⟨b, hfun⟩


theorem bc40_armCutGeometryFixed_false_of_idempotentDownArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s)
    (hidem : ∀ b : Site d → Site d,
      (∀ x, x ∈ box d n → IsTrifurcation d ω x →
        b x ∈ box d n ∧ Connected d ω x (b x) ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) →
      b (b t) = b t ∧ b t ≠ s ∧ b t ≠ t) :
    ¬ bc39_ArmCutGeometryFixed ω n := by
  rintro ⟨b, hdata, hclauses⟩
  obtain ⟨_hloc, hself, hfun⟩ := hclauses t s htbox htri hadj
  obtain ⟨hbbt, hbts, hbtt⟩ := hidem b hdata
  
  have hreach : Connected d (removeSite t ω) (b (b t)) s := hfun (b t) hbts hbtt
  rw [hbbt] at hreach
  exact hself hreach


end StatMech.Walls
