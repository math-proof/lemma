/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySwitching.Part2
import Instance.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def boundarySourceCurrentRawMass
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources : Finset V) (m : EdgeCurrent G) : ENNReal :=
  ENNReal.ofReal
    (if sources G (ofEdgeFun G m) ∩ interior = internalSources then
      weight G beta J (ofEdgeFun G m)
    else 0)

end StatMech.FrontierB
