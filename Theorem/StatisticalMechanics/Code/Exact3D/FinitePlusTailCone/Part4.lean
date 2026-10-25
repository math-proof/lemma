/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone.Part4


namespace StatMech

namespace Exact3D

namespace FinitePlusTailConeCertificate

variable {n : ℕ} {α : Type*}


theorem cone_step
    (C : FinitePlusTailConeCertificate n α)
    {η : ℝ} (hη : 0 ≤ η) {x : FinitePlusTailState n α}
    (hx : C.cone η x) :
    C.cone η (C.contraction.map x) := by
  have hcone_rhs_nonneg : 0 ≤ η * |C.thermal x| :=
    mul_nonneg hη (abs_nonneg _)
  calc
    C.stableSize (C.contraction.map x) ≤
        C.stableStepConstant * C.stableSize x :=
      C.stable_step_bound x
    _ ≤ C.stableStepConstant * (η * |C.thermal x|) :=
      mul_le_mul_of_nonneg_left hx C.stableStepConstant_nonneg
    _ ≤ |C.thermalMultiplier| * (η * |C.thermal x|) :=
      mul_le_mul_of_nonneg_right C.stable_dominated hcone_rhs_nonneg
    _ = η * |C.thermal (C.contraction.map x)| := by
      rw [C.thermal_step x, abs_mul]
      ring


theorem thermal_iterate_eq
    (C : FinitePlusTailConeCertificate n α)
    (k : ℕ) (x : FinitePlusTailState n α) :
    C.thermal (C.contraction.iterate k x) =
      C.thermalMultiplier ^ k * C.thermal x := by
  induction k with
  | zero =>
      simp [FinitePlusTailLipschitzCertificate.iterate]
  | succ k ih =>
      calc
        C.thermal (C.contraction.iterate (k + 1) x) =
            C.thermal (C.contraction.map (C.contraction.iterate k x)) := rfl
        _ =
            C.thermalMultiplier *
              C.thermal (C.contraction.iterate k x) :=
          C.thermal_step (C.contraction.iterate k x)
        _ =
            C.thermalMultiplier *
              (C.thermalMultiplier ^ k * C.thermal x) := by
          rw [ih]
        _ =
            C.thermalMultiplier ^ (k + 1) * C.thermal x := by
          rw [pow_succ']
          ring


theorem stableSize_iterate_le
    (C : FinitePlusTailConeCertificate n α)
    (k : ℕ) (x : FinitePlusTailState n α) :
    C.stableSize (C.contraction.iterate k x) ≤
      C.stableStepConstant ^ k * C.stableSize x := by
  induction k with
  | zero =>
      simp [FinitePlusTailLipschitzCertificate.iterate]
  | succ k ih =>
      calc
        C.stableSize (C.contraction.iterate (k + 1) x) =
            C.stableSize
              (C.contraction.map (C.contraction.iterate k x)) := rfl
        _ ≤
            C.stableStepConstant *
              C.stableSize (C.contraction.iterate k x) :=
          C.stable_step_bound (C.contraction.iterate k x)
        _ ≤
            C.stableStepConstant *
              (C.stableStepConstant ^ k * C.stableSize x) :=
          mul_le_mul_of_nonneg_left ih C.stableStepConstant_nonneg
        _ =
            C.stableStepConstant ^ (k + 1) * C.stableSize x := by
          rw [pow_succ']
          ring


theorem cone_iterate
    (C : FinitePlusTailConeCertificate n α)
    {η : ℝ} (hη : 0 ≤ η) {x : FinitePlusTailState n α}
    (hx : C.cone η x) (k : ℕ) :
    C.cone η (C.contraction.iterate k x) := by
  induction k with
  | zero =>
      simpa [FinitePlusTailLipschitzCertificate.iterate] using hx
  | succ _ ih =>
      exact C.cone_step hη ih


theorem cone_iterate_closed_form
    (C : FinitePlusTailConeCertificate n α)
    {η : ℝ} (hη : 0 ≤ η) {x : FinitePlusTailState n α}
    (hx : C.cone η x) (k : ℕ) :
    C.stableSize (C.contraction.iterate k x) ≤
      η * |C.thermalMultiplier ^ k * C.thermal x| := by
  have hcone := C.cone_iterate hη hx k
  simpa [cone, C.thermal_iterate_eq k x] using hcone

end FinitePlusTailConeCertificate
end Exact3D
end StatMech
