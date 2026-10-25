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
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part7
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def leeYangAnchorChoiceFactor (z : LeeYangVar G → ℂ) (v : V) (b : Bool) : ℂ :=
  if b then z (leeYangAnchor G v) else 1

noncomputable def leeYangEdgeChoiceFactor (beta : ℝ) (z : LeeYangVar G → ℂ)
    (e : ↑G.edgeFinset) (b : Bool × Bool) : ℂ :=
  (if b.1 = b.2 then 1 else (Real.exp (-2 * beta) : ℂ)) *
    (if b.1 then z (leeYangHalf G (leeYangEndpoint0 G e) e) else 1) *
    (if b.2 then z (leeYangHalf G (leeYangEndpoint1 G e) e) else 1)

end StatMech.FrontierA
