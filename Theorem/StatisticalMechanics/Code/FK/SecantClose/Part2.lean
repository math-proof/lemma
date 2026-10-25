/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.PressureDiff
import Theorem.StatisticalMechanics.Code.FK.TiltSecant.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
import Def.StatisticalMechanics.Code.FK.SecantClose.Part2
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


theorem fsc_secant (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : fsc_FreeEnergyData d N eb) :
    ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p'
        ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p := by
  obtain ⟨g, hg, hwired, hfree⟩ := hdata
  intro p hp p' hp' hlt
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hp'0, hp'1⟩ := hp'
  
  set t := fsc_logit p with ht
  set t' := fsc_logit p' with ht'
  have hpt : fsc_logistic t = p := fsc_logistic_logit hp0 hp1
  have hpt' : fsc_logistic t' = p' := fsc_logistic_logit hp'0 hp'1
  
  have htlt : t' < t := by
    by_contra hge
    rw [not_lt] at hge
    have := fsc_logistic_strictMono.monotone hge
    rw [hpt, hpt'] at this
    linarith
  
  have hw : wiredEdgeDensity d 2 (edgeIncl d N eb) p' = pressureRightDeriv g t' := by
    rw [← hpt']; exact hwired t'
  have hf : freeEdgeDensity d 2 (edgeIncl d N eb) p = pressureLeftDeriv g t := by
    rw [← hpt]; exact hfree t
  rw [hw, hf]
  
  exact pressureRightDeriv_le_leftDeriv_of_lt hg htlt


end FK
end StatMech
