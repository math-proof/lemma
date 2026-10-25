/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundarySourceParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.BoundarySourceParity
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def boundarySourceParityPMF
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1)
      interior internalSources) : PMF (Finset (Sym2 V)) :=
  PMF.map (currentParitySupport G)
    (boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta
      (fun _ ↦ zero_le_one) interior internalSources hpos)

end StatMech.FrontierB
