/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part8
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangHalfEdgeProduct_eq_sum_choices (beta : ℝ) :
    leeYangHalfEdgeProduct G beta =
      fun z ↦ ∑ x : (V → Bool) × (↑G.edgeFinset → Bool × Bool),
        leeYangChoiceTerm G beta x z := by
  funext z
  rw [leeYangHalfEdgeProduct_eq]
  unfold leeYangAnchorProduct leeYangEdgeProduct leeYangChoiceTerm
  simp_rw [← sum_leeYangAnchorChoiceFactor G z,
    ← sum_leeYangEdgeChoiceFactor G beta z]
  rw [Fintype.prod_sum, Fintype.prod_sum, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_mul]

end StatMech.FrontierA
