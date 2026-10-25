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
import Theorem.StatisticalMechanics.Code.Ising.PeierlsUncond.Part2
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def crossEdges (K : Set (Site d)) (B : Finset (Sym2 (Site d))) :
    Finset (Sym2 (Site d)) :=
  B.filter (crosses K)


noncomputable def contourLen (K : Set (Site d)) (B : Finset (Sym2 (Site d))) : ℕ :=
  (crossEdges K B).card


noncomputable def crossEdgeBond (K : Set (Site d)) (σ : ConfigSpace (Site d))
    (e : Sym2 (Site d)) : ℝ :=
  Sym2.lift ⟨fun x y => if (x ∈ K ↔ y ∉ K) then bond σ s(x, y) else 0, by
    intro x y; simp only
    rw [bond_mk, bond_mk, mul_comm (spin σ x)]
    by_cases h : (x ∈ K ↔ y ∉ K)
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto)]⟩ e

end Ising
end StatMech
