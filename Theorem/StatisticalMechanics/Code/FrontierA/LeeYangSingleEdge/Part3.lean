/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangDisjointUnion
import Instance.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


theorem leeYangComplexPolynomial_finiteMatching (n : ℕ) (beta : ℝ) :
    leeYangComplexPolynomial (finiteMatching n) beta =
      (leeYangComplexPolynomial twoVertexEdge beta) ^ n := by
  induction n with
  | zero =>
      change leeYangComplexPolynomial (⊥ : SimpleGraph Empty) beta = _
      rw [leeYangComplexPolynomial_bot]
      simp
  | succ n ih =>
      change leeYangComplexPolynomial (twoVertexEdge ⊕g finiteMatching n) beta = _
      rw [leeYangComplexPolynomial_sum, ih, pow_succ]
      ring


theorem finiteMatching_hasLeeYangCircle (n : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta) :
    HasLeeYangCircle (finiteMatching n) beta := by
  induction n with
  | zero =>
      intro z hz
      exact leeYangComplexPolynomial_bot_root_norm beta hz
  | succ n ih =>
      simpa only [finiteMatching] using
        HasLeeYangCircle.sum twoVertexEdge (finiteMatching n)
          (hasLeeYangCircle_twoVertexEdge hbeta) ih

end StatMech.FrontierA
