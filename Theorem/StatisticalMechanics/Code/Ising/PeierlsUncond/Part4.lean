/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsFull.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Def.StatisticalMechanics.Code.Ising.PeierlsUncond.Part4
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


lemma sum_crossEdgeBond_event (K : Set (Site d)) (σ : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) (h : ContourEvent K B σ) :
    (∑ e ∈ B, crossEdgeBond K σ e) = - (contourLen K B : ℝ) := by
  rw [sum_crossEdgeBond, Finset.sum_congr rfl (fun e he => h e he)]
  simp [contourLen]


end Ising
end StatMech
