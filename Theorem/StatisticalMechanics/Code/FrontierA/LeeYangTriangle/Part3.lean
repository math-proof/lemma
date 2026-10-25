/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Instance.StatisticalMechanics.Code.FrontierA.LeeYangTriangle.Part3
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


theorem finiteTriangleGraph_hasLeeYangCircle (t : ℕ) {beta : ℝ}
    (hbeta : 0 ≤ beta) : HasLeeYangCircle (finiteTriangleGraph t) beta := by
  induction t with
  | zero =>
      intro z hz
      exact leeYangComplexPolynomial_bot_root_norm beta hz
  | succ t ih =>
      simpa only [finiteTriangleGraph] using
        HasLeeYangCircle.sum threeVertexTriangle (finiteTriangleGraph t)
          (hasLeeYangCircle_threeVertexTriangle hbeta) ih


end StatMech.FrontierA
