/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine
open scoped symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

noncomputable def gaugeWilsonClosedEquiv
    (incidence : P → Finset E) (L : Finset E) (D : Finset P)
    (hD : HasWilsonBoundary incidence D L) :
    {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L} ≃
      {B : Finset P // B ∈ gaugeClosedSurfaceFamily incidence} where
  toFun A := ⟨A.1 ∆ D,
    (mem_gaugeClosedSurfaceFamily_iff incidence _).2
      ((hasWilsonBoundary_iff_symmDiff_closed incidence L D A.1 hD).1
        ((mem_gaugeWilsonSurfaceFamily_iff incidence L A.1).1 A.2))⟩
  invFun B := ⟨B.1 ∆ D,
    (mem_gaugeWilsonSurfaceFamily_iff incidence L _).2
      ((hasWilsonBoundary_iff_symmDiff_closed incidence L D (B.1 ∆ D) hD).2
        (by simpa using
          (mem_gaugeClosedSurfaceFamily_iff incidence B.1).1 B.2))⟩
  left_inv A := by
    apply Subtype.ext
    simp
  right_inv B := by
    apply Subtype.ext
    simp


end StatMech.FrontierA
