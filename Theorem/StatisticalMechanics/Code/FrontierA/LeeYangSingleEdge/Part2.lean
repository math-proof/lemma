/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangDisjointUnion
import Def.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part2
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


theorem HasLeeYangCircle.sum {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] {beta : ℝ}
    (hG : HasLeeYangCircle G beta) (hH : HasLeeYangCircle H beta) :
    HasLeeYangCircle (G ⊕g H) beta := by
  intro z hz
  rw [leeYangComplexPolynomial_sum G H, Polynomial.eval_mul] at hz
  rcases mul_eq_zero.mp hz with hzG | hzH
  · exact hG z hzG
  · exact hH z hzH


theorem hasLeeYangCircle_twoVertexEdge {beta : ℝ} (hbeta : 0 ≤ beta) :
    HasLeeYangCircle twoVertexEdge beta := by
  intro z hz
  exact leeYang_twoVertexEdge_root_norm hbeta hz


end StatMech.FrontierA
