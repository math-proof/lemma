/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWStripSymmetry.Part5
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperViaFK.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWQOneMixedSquare.Part2
open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.FK

open StatMech.RSW.Box

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def rq1_mixedSquareWiring (n : ℕ) : SimpleGraph (boxVerts 2 n) where
  Adj x y := x ≠ y ∧
    (((x : Site 2) 1 = -(n : ℤ) ∧ (y : Site 2) 1 = -(n : ℤ)) ∨
      ((x : Site 2) 1 = (n : ℤ) ∧ (y : Site 2) 1 = (n : ℤ)))
  symm := by
    constructor
    rintro x y ⟨hne, h⟩
    refine ⟨Ne.symm hne, ?_⟩
    rcases h with h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2, h.1⟩
  loopless := ⟨fun x h => h.1 rfl⟩

end Universality
end StatMech
