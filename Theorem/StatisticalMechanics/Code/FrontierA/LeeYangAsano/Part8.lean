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
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part7
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem sum_leeYangAnchorChoiceFactor (z : LeeYangVar G → ℂ) (v : V) :
    ∑ b : Bool, leeYangAnchorChoiceFactor G z v b = 1 + z (leeYangAnchor G v) := by
  simp [leeYangAnchorChoiceFactor, add_comm]

omit [DecidableEq V] in
theorem sum_leeYangEdgeChoiceFactor (beta : ℝ) (z : LeeYangVar G → ℂ)
    (e : ↑G.edgeFinset) :
    ∑ b : Bool × Bool, leeYangEdgeChoiceFactor G beta z e b =
      leeYangNormalizedEdgeFactor G beta e z := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  unfold leeYangEdgeChoiceFactor
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false]
  have hout := leeYang_endpoints_mk G e
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [leeYangNormalizedEdgeFactor, Sym2.lift_mk] at ⊢ hout
      have h0 : leeYangEndpoint0 G ⟨s(u, v), he⟩ = u ∧
          leeYangEndpoint1 G ⟨s(u, v), he⟩ = v ∨
          leeYangEndpoint0 G ⟨s(u, v), he⟩ = v ∧
          leeYangEndpoint1 G ⟨s(u, v), he⟩ = u :=
        Sym2.eq_iff.mp hout
      rcases h0 with h0 | h0 <;> rw [h0.1, h0.2] <;> ring

end StatMech.FrontierA
