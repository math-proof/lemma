/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousBoundaryParityAvoidance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeBoundaryCurrentConditionalPMF
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance.Part3
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def inhomogeneousBoundaryParityPartition
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V) : ℝ :=
  ∑ H ∈ G.edgeFinset.powerset,
    if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then
      highTempSubgraphWeight beta J H else 0

noncomputable def inhomogeneousBoundaryParityAvoidSum
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V)
    (F : Finset (Sym2 V)) : ℝ :=
  ∑ H ∈ G.edgeFinset.powerset,
    if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ ∧ Disjoint H F then
      highTempSubgraphWeight beta J H else 0

end StatMech.FrontierB
