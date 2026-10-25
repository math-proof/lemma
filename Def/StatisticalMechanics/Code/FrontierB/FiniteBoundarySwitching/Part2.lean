/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteNormalizedSwitching
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundaryCurrentLaw.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentPairLaw.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySwitching
open scoped symmDiff


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def boundarySourceSectorSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources : Finset V) : ℝ :=
  ∑ A : Finset V,
    if A ∩ interior = internalSources then currentSum G beta J A else 0


noncomputable def boundarySourceCurrentSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources : Finset V) : ℝ :=
  ∑' m : EdgeCurrent G,
    if sources G (ofEdgeFun G m) ∩ interior = internalSources then
      weight G beta J (ofEdgeFun G m)
    else 0


noncomputable def boundarySourceGatedPairSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources exactSecondSources : Finset V)
    (P : Current V → Prop) [DecidablePred P] : ℝ :=
  ∑ A : Finset V,
    if A ∩ interior = internalSources then
      gatedSourcePairSum G beta J A exactSecondSources P
    else 0


end StatMech.FrontierB
