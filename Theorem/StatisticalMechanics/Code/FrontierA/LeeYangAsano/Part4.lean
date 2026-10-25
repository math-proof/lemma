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
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part3
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangContractList_multiAffine (L : List (V × ↑G.edgeFinset))
    (p : (LeeYangVar G → ℂ) → ℂ) (hp : IsMultiAffine p) :
    IsMultiAffine (leeYangContractList G L p) := by
  induction L generalizing p with
  | nil => exact hp
  | cons x L ih =>
      simp only [leeYangContractList, List.foldl_cons]
      apply ih
      apply asanoContract_multiAffine p hp
      simp [leeYangAnchor, leeYangHalf]

theorem leeYangContractList_stable (L : List (V × ↑G.edgeFinset))
    (p : (LeeYangVar G → ℂ) → ℂ) (hpAff : IsMultiAffine p)
    (hpStable : PolydiscStable p) :
    PolydiscStable (leeYangContractList G L p) := by
  induction L generalizing p with
  | nil => exact hpStable
  | cons x L ih =>
      simp only [leeYangContractList, List.foldl_cons]
      apply ih
      · apply asanoContract_multiAffine p hpAff
        simp [leeYangAnchor, leeYangHalf]
      · apply asanoContract_stable p hpAff hpStable
        simp [leeYangAnchor, leeYangHalf]

end StatMech.FrontierA
