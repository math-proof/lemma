/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone


namespace StatMech

namespace Exact3D

namespace FinitePlusTailState

variable {n : ℕ} {α : Type*}


theorem mixedNorm_nonneg (x : FinitePlusTailState n α) :
    0 ≤ mixedNorm x :=
  dist_nonneg x origin

end FinitePlusTailState

namespace FinitePlusTailLipschitzCertificate

variable {n : ℕ} {α : Type*}


theorem mixedNorm_map_le_mul_of_map_origin
    (C : FinitePlusTailLipschitzCertificate n α)
    (h0 :
      C.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
        FinitePlusTailState.origin)
    (x : FinitePlusTailState n α) :
    FinitePlusTailState.mixedNorm (C.map x) ≤
      C.c * FinitePlusTailState.mixedNorm x := by
  simpa [FinitePlusTailState.mixedNorm, h0] using
    C.mixed_lipschitz x
      (FinitePlusTailState.origin : FinitePlusTailState n α)


theorem map_mem_thermalStableCone_of_c_le_abs_thermal
    (C : FinitePlusTailLipschitzCertificate n α)
    (h0 :
      C.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
        FinitePlusTailState.origin)
    {thermal η t : ℝ} {s : FinitePlusTailState n α}
    (hη : 0 ≤ η)
    (hdom : C.c ≤ |thermal|)
    (hs : FinitePlusTailState.ThermalStableCone η t s) :
    FinitePlusTailState.ThermalStableCone η (thermal * t) (C.map s) := by
  have hcone_rhs_nonneg : 0 ≤ η * |t| :=
    mul_nonneg hη (abs_nonneg _)
  calc
    FinitePlusTailState.mixedNorm (C.map s) ≤
        C.c * FinitePlusTailState.mixedNorm s :=
      C.mixedNorm_map_le_mul_of_map_origin h0 s
    _ ≤ C.c * (η * |t|) :=
      mul_le_mul_of_nonneg_left hs C.c_nonneg
    _ ≤ |thermal| * (η * |t|) :=
      mul_le_mul_of_nonneg_right hdom hcone_rhs_nonneg
    _ = η * |thermal * t| := by
      rw [abs_mul]
      ring


theorem iterate_origin_of_map_origin
    (C : FinitePlusTailLipschitzCertificate n α)
    (h0 :
      C.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
        FinitePlusTailState.origin)
    (k : ℕ) :
    C.iterate k
        (FinitePlusTailState.origin : FinitePlusTailState n α) =
      FinitePlusTailState.origin := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, ih, h0]


theorem iterate_mem_thermalStableCone_of_c_le_abs_thermal
    (C : FinitePlusTailLipschitzCertificate n α)
    (h0 :
      C.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
        FinitePlusTailState.origin)
    {thermal η t : ℝ} {s : FinitePlusTailState n α}
    (hη : 0 ≤ η)
    (hdom : C.c ≤ |thermal|)
    (hs : FinitePlusTailState.ThermalStableCone η t s)
    (k : ℕ) :
    FinitePlusTailState.ThermalStableCone η (thermal ^ k * t)
      (C.iterate k s) := by
  induction k with
  | zero =>
      simpa [iterate] using hs
  | succ k ih =>
      have hstep :=
        C.map_mem_thermalStableCone_of_c_le_abs_thermal
          h0 hη hdom ih
      simpa [iterate, pow_succ', mul_assoc] using hstep

end FinitePlusTailLipschitzCertificate
end Exact3D
end StatMech
