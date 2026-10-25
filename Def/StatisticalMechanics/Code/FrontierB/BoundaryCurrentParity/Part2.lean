/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def boundaryParityPMF (beta : ℝ) (hbeta : 0 ≤ beta)
    (interior : Finset V) : PMF (Finset (Sym2 V)) :=
  PMF.map (currentParitySupport G)
    (boundaryCurrentPMF G beta (fun _ => 1) hbeta
      (fun _ => zero_le_one) interior)

end StatMech.FrontierB
