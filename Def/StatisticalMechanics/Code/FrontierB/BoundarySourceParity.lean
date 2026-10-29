/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw.Part4
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def boundarySourceParityAllowed (interior internalSources : Finset V)
    (H : Finset (Sym2 V)) : Prop :=
  H ⊆ G.edgeFinset ∧
    sources G (edgeIndicatorCurrent H) ∩ interior = internalSources

noncomputable def boundarySourceParityRawMass (beta : ℝ)
    (interior internalSources : Finset V)
    (H : Finset (Sym2 V)) : ENNReal := by
  classical
  exact ENNReal.ofReal
    (if boundarySourceParityAllowed G interior internalSources H then
      Real.tanh beta ^ H.card else 0)

noncomputable def boundarySourceParityPartition (beta : ℝ)
    (interior internalSources : Finset V) : ℝ := by
  classical
  exact ∑ H : Finset (Sym2 V),
    if boundarySourceParityAllowed G interior internalSources H then
      Real.tanh beta ^ H.card else 0

end StatMech.FrontierB
