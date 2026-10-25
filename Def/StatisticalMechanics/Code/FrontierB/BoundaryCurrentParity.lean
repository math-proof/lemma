/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def boundaryParityAllowed (interior : Finset V)
    (H : Finset (Sym2 V)) : Prop :=
  H ⊆ G.edgeFinset ∧
    sources G (edgeIndicatorCurrent H) ∩ interior = ∅

noncomputable def boundaryParityRawMass (beta : ℝ)
    (interior : Finset V) (H : Finset (Sym2 V)) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal
    (if boundaryParityAllowed G interior H then
        Real.tanh beta ^ H.card else 0)

noncomputable def boundaryParityPartition (beta : ℝ)
    (interior : Finset V) : ℝ := by
  classical
  exact ∑ H : Finset (Sym2 V),
    if boundaryParityAllowed G interior H then
        Real.tanh beta ^ H.card else 0

noncomputable def boundaryParityAvoidSum (beta : ℝ)
    (interior : Finset V) (F : Finset (Sym2 V)) : ℝ := by
  classical
  exact ∑ H : Finset (Sym2 V),
    if boundaryParityAllowed G interior H ∧ Disjoint H F then
      Real.tanh beta ^ H.card else 0

end StatMech.FrontierB
