/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc45depthwalk.Part4
import Def.StatisticalMechanics.Code.Walls.bc46funnelproof
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc46_armCutGeometryFixed'_of_armFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_ArmFunnelGeometry ω n) : bc40_ArmCutGeometryFixed' ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  refine ⟨b, hdata, ?_⟩
  intro t s htbox htri hadj
  obtain ⟨hloc, hself, hlink⟩ := hclauses t s htbox htri hadj
  refine ⟨hloc, hself, ?_⟩
  intro x hxt hxs
  
  exact (hlink x hxt hxs).symm.trans hxs


end StatMech.Walls
