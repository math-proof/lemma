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
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part4
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangContractedProduct_multiAffine (beta : ℝ) :
    IsMultiAffine (leeYangContractedProduct G beta) :=
  leeYangContractList_multiAffine G _ _ (leeYangHalfEdgeProduct_multiAffine G beta)

theorem leeYangContractedProduct_stable {beta : ℝ} (hbeta : 0 ≤ beta) :
    PolydiscStable (leeYangContractedProduct G beta) :=
  leeYangContractList_stable G _ _ (leeYangHalfEdgeProduct_multiAffine G beta)
    (leeYangHalfEdgeProduct_stable G hbeta)

end StatMech.FrontierA
