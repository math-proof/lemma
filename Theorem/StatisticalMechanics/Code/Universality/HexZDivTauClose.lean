/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3


namespace StatMech.Universality

open Filter Topology Complex HexWalk

open scoped Topology BigOperators


theorem hzd_not_summable_const {c : ℝ} (hc : c ≠ 0) :
    ¬ Summable (fun _ : ℕ => c) := by
  intro hsum
  have h0 := hsum.tendsto_atTop_zero
  have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  exact hc (tendsto_nhds_unique hconst h0)


theorem hzd_not_summable_of_const_inj {I : Type*} (w : I → ℝ) (c : ℝ) (hc : 0 < c)
    (g : ℕ → I) (hg : Function.Injective g) (hconst : ∀ n, w (g n) = c) :
    ¬ Summable w := by
  intro hsum
  have hcomp : Summable (fun n : ℕ => w (g n)) := hsum.comp_injective hg
  have heq : (fun n : ℕ => w (g n)) = fun _ : ℕ => c := by
    funext n; exact hconst n
  rw [heq] at hcomp
  exact hzd_not_summable_const (ne_of_gt hc) hcomp


theorem hzd_vertShift_injective (mid period : ℂ) (hp : period ≠ 0) :
    Function.Injective (fun h : ℕ => mid + period * (h : ℂ)) := by
  intro a b hab
  simp only [add_right_inj] at hab
  exact_mod_cast mul_left_cancel₀ hp hab


theorem hzd_sawwt_vertShift (mid period : ℂ) (head : ℤ) (x : ℝ) (turns : List ℤ)
    (h : ℕ) :
    hexSAWwt (mid + period * (h : ℂ)) head x turns = hexSAWwt mid head x turns :=
  hexW2S_hexSAWwt_mid_indep mid (mid + period * (h : ℂ)) head x turns


end StatMech.Universality
