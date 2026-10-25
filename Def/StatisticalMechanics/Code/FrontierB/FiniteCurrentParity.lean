/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def freeParityPartition (beta : ℝ) : ℝ :=
  ∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
    Real.tanh beta ^ H.card

noncomputable def freeParityAvoidSum (beta : ℝ) (F : Finset (Sym2 V)) : ℝ :=
  ∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
    if Disjoint H F then Real.tanh beta ^ H.card else 0

noncomputable def deletedEdgeCoupling (F : Finset (Sym2 V)) : Sym2 V → ℝ :=
  fun e => if e ∈ F then 0 else 1

noncomputable def edgeSpinSum (F : Finset (Sym2 V)) (s : ConfigSpace V) : ℝ :=
  ∑ e ∈ F, bond s e

end StatMech.FrontierB
