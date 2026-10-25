/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusProof
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset BigOperators CoxeterGroup


namespace PerronFrobeniusProof

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- **Perron–Frobenius instance**: every off-diagonal-nonpositive real matrix on a nonempty index
type automatically satisfies the `PerronFrobeniusProperty`. -/
instance perronFrobeniusInstance (f : B → B → ℝ) [Nonempty B] :
    PerronFrobeniusProperty f where
  kernel_span := by
    intro hIndecomp hPSD hNotPD hOffDiag
    obtain ⟨v₀, hv₀_ne, hQv₀⟩ := hNotPD

    have hPSD' : ∀ u : B → ℝ, QF f u ≥ 0 := hPSD
    have hQv₀' : QF f v₀ = 0 := hQv₀

    have hQv₀_abs : QF f (fun b => |v₀ b|) = 0 := by
      have h1 := QF_abs_le f v₀ hOffDiag
      have h2 := hPSD' (fun b => |v₀ b|)
      linarith

    have hv₀_abs_ne : (fun b => |v₀ b|) ≠ 0 := by
      intro h
      have : ∀ b, v₀ b = 0 := fun b => abs_eq_zero.mp (congr_fun h b)
      exact hv₀_ne (funext this)

    have hv₀_abs_pos := nonneg_kernel_pos f (fun b => |v₀ b|) hPSD' hQv₀_abs
      (fun b => abs_nonneg _) hv₀_abs_ne hOffDiag hIndecomp

    refine ⟨fun b => |v₀ b|, hv₀_abs_pos, ?_⟩

    intro w hQw
    exact kernel_scalar_multiple f (fun b => |v₀ b|) w hPSD' hv₀_abs_pos hQv₀_abs hQw hOffDiag hIndecomp

end PerronFrobeniusProof
