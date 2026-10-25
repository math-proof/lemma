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
import Theorem.StatisticalMechanics.Code.Walls.bc46funnelproof.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc46_clawLab (c v : Fin 10) : Fin 10 :=
  if c = 0 then      
    (if v = 0 then 0
     else if v = 1 ∨ v = 4 ∨ v = 5 then 1
     else if v = 2 ∨ v = 6 ∨ v = 7 then 2 else 3)
  else if c = 1 then 
    (if v = 1 then 1 else if v = 4 then 4 else if v = 5 then 5 else 0)
  else if c = 2 then 
    (if v = 2 then 2 else if v = 6 then 6 else if v = 7 then 7 else 0)
  else               
    (if v = 3 then 3 else if v = 8 then 8 else if v = 9 then 9 else 0)


def bc46_clawB : Fin 10 → Fin 10 := ![5, 4, 6, 8, 4, 5, 6, 7, 8, 9]


end StatMech.Walls
