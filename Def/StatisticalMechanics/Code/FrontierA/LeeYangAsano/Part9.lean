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
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part9
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def leeYangChoiceWeight (beta : ℝ)
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)) : ℂ :=
  ∏ e : ↑G.edgeFinset,
    if (x.2 e).1 = (x.2 e).2 then 1 else (Real.exp (-2 * beta) : ℂ)

noncomputable def leeYangChoiceSelected
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)) :
    LeeYangVar G → Bool
  | Sum.inl v => x.1 v
  | Sum.inr (v, e) =>
      if v = leeYangEndpoint0 G e then (x.2 e).1
      else if v = leeYangEndpoint1 G e then (x.2 e).2
      else false

noncomputable def leeYangChoiceSupport
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool)) :
    Finset (LeeYangVar G) :=
  Finset.univ.filter fun k ↦ leeYangChoiceSelected G x k = true

end StatMech.FrontierA
