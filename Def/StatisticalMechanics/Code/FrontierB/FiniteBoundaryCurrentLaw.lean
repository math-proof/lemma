/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundaryCurrentLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentTightness
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def boundaryCurrentSum (beta : ℝ) (J : Sym2 V → ℝ)
    (interior : Finset V) : ℝ :=
  ∑' m : EdgeCurrent G,
    if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
      weight G beta J (ofEdgeFun G m) else 0


noncomputable def boundaryCurrentRawMass (beta : ℝ) (J : Sym2 V → ℝ)
    (interior : Finset V) (m : EdgeCurrent G) : ℝ≥0∞ :=
  ENNReal.ofReal
    (if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
      weight G beta J (ofEdgeFun G m) else 0)


end StatMech.FrontierB
