/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone.Part2


namespace StatMech

namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type*}


theorem step_origin (H : FinitePlusTailHyperbolicSplitting n α) :
    H.step origin = origin := by
  apply Prod.ext
  · simp [step, origin]
  · simpa [step, origin] using H.stable_origin


theorem iterate_origin (H : FinitePlusTailHyperbolicSplitting n α) (k : ℕ) :
    H.iterate k origin = origin := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, ih, H.step_origin]


theorem iterate_fst_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (k : ℕ) (x : State n α) :
    (H.iterate k x).1 = H.thermal ^ k * x.1 := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, step, ih, pow_succ', mul_assoc]


theorem iterate_snd_eq
    (H : FinitePlusTailHyperbolicSplitting n α)
    (k : ℕ) (x : State n α) :
    (H.iterate k x).2 = H.stable.iterate k x.2 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      calc
        (H.iterate (k + 1) x).2 =
            (H.step (H.iterate k x)).2 := rfl
        _ = H.stable.map (H.iterate k x).2 := rfl
        _ = H.stable.map (H.stable.iterate k x.2) := by
          rw [ih]
        _ = H.stable.iterate (k + 1) x.2 := rfl


end FinitePlusTailHyperbolicSplitting
end Exact3D
end StatMech
