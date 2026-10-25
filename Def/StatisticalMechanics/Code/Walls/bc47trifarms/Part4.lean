/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc46funnelproof.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc47trifarms.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc47_IsClassicalTrifurcation (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    (IsOpenEdge d ω x a₁ ∧ IsOpenEdge d ω x a₂ ∧ IsOpenEdge d ω x a₃) ∧
    ((cluster d (removeSite x ω) a₁).Infinite ∧ (cluster d (removeSite x ω) a₂).Infinite ∧
      (cluster d (removeSite x ω) a₃).Infinite) ∧
    (¬ Connected d (removeSite x ω) a₁ a₂ ∧
     ¬ Connected d (removeSite x ω) a₁ a₃ ∧
     ¬ Connected d (removeSite x ω) a₂ a₃)


end StatMech.Walls
