/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Def.StatisticalMechanics.Code.FK.BoxTiling
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice SimpleGraph

variable {d : ℕ}


theorem bxt_g_eq (d : ℕ) (t : ℝ) (n : ℕ) :
    ivp2_tiltFreeEnergy (boxGraph d n) 2 t
      = - (bxt_u d t n / bxt_E d n) + Real.log (1 + Real.exp t) := by
  unfold ivp2_tiltFreeEnergy bxt_u bxt_E
  ring


theorem bxt_E_nonneg (d n : ℕ) : 0 ≤ bxt_E d n := by
  unfold bxt_E; positivity


theorem bxt_perVolume_doubling_step
    {a A e E K c i : ℝ} (he : 0 < e) (hE : 0 < E) (hc : 0 ≤ c) (hi : 0 ≤ i)
    (hA : A ≤ K * a + i * c) (hedge : |K * e - E| ≤ i) :
    - (a / e) - (|a| / e + c) * (i / E) ≤ - (A / E) := by
  have hmain : A / E - a / e ≤ (|a| / e + c) * (i / E) := by
    have hstep1 : A / E ≤ (K * a + i * c) / E := (div_le_div_iff_of_pos_right hE).mpr hA
    have hkey : (K * a + i * c) / E - a / e = a * (K * e - E) / (e * E) + i * c / E := by
      field_simp; ring
    have hbound : a * (K * e - E) / (e * E) ≤ (|a| / e) * (i / E) := by
      rw [div_mul_div_comm]
      apply (div_le_div_iff_of_pos_right (by positivity)).mpr
      calc a * (K * e - E) ≤ |a * (K * e - E)| := le_abs_self _
        _ = |a| * |K * e - E| := by rw [abs_mul]
        _ ≤ |a| * i := by apply mul_le_mul_of_nonneg_left hedge (abs_nonneg a)
    have hicE : i * c / E = c * (i / E) := by ring
    calc A / E - a / e ≤ (K * a + i * c) / E - a / e := by linarith
      _ = a * (K * e - E) / (e * E) + i * c / E := hkey
      _ ≤ (|a| / e) * (i / E) + c * (i / E) := by rw [hicE]; linarith [hbound]
      _ = (|a| / e + c) * (i / E) := by ring
  linarith


end FK
end StatMech
