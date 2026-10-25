/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc41rootside.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc42rootward.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc43rootparent
import Theorem.StatisticalMechanics.Code.Walls.bc44rootwalk.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc45depthwalk
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


open Classical in


noncomputable def bc45_armDepthRank (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Site d → ℕ ×ₗ ℕ :=
  fun v => toLex (bc45_dep ω n v, bc45_idx ω n v)

open Classical in


noncomputable def bc45_armForestPar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Site d → Site d :=
  fun v => if hv : v ∈ tfc_trifFinset ω n then
    (bc38_parentTo (bc37_armAdjGraph ω n) (bc45_root ω n) ⟨v, hv⟩).1 else v


end StatMech.Walls
