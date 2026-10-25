/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part6
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


noncomputable def jsi_arcWalk (col : ℤ → ℤ)
    (hsh : ∀ r : ℤ, col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1)
    (c : ℤ) :
    (n : ℕ) → (hypercubicLattice 2).Walk (jsi_cell (col c) c) (jsi_cell (col (c + n)) (c + n))
  | 0 => (SimpleGraph.Walk.nil).copy rfl (by rw [jsi_cell_eq]; norm_num)
  | (n + 1) => by
      have prev := jsi_arcWalk col hsh c n
      have vstep := jsi_vstep_adj (col (c + (n : ℤ))) (c + (n : ℤ))
      have hc := jsi_hconn (col (c + (n : ℤ))) (col (c + (n : ℤ) + 1)) (c + (n : ℤ) + 1)
        (by have := hsh (c + (n : ℤ)); omega)
      have step : (hypercubicLattice 2).Walk (jsi_cell (col (c + (n : ℤ))) (c + (n : ℤ)))
                    (jsi_cell (col (c + (n : ℤ) + 1)) (c + (n : ℤ) + 1)) :=
        SimpleGraph.Walk.cons vstep hc
      refine (prev.append step).copy rfl ?_
      have heq : c + (n : ℤ) + 1 = c + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [jsi_cell_eq]; exact ⟨by rw [heq], heq⟩


end Lattice
end StatMech
