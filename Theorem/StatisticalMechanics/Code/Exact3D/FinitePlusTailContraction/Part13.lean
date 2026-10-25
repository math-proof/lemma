/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part10
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailLipschitzCertificate

variable {n : ℕ} {α : Type*}


theorem fixedPoint_isFixed
    (C : FinitePlusTailLipschitzCertificate n α) :
    C.map C.fixedPoint = C.fixedPoint := by
  have hfixed : Function.IsFixedPt C.map C.fixedPoint :=
    C.contractingWith.fixedPoint_isFixedPt
  simpa [fixedPoint, Function.IsFixedPt] using hfixed


theorem fixedPoint_unique
    (C : FinitePlusTailLipschitzCertificate n α)
    {x y : FinitePlusTailState n α}
    (hx : C.map x = x) (hy : C.map y = y) : x = y :=
  C.contractingWith.fixedPoint_unique' hx hy


theorem eq_fixedPoint_of_isFixed
    (C : FinitePlusTailLipschitzCertificate n α)
    {x : FinitePlusTailState n α} (hx : C.map x = x) :
    x = C.fixedPoint :=
  C.contractingWith.fixedPoint_unique hx


theorem exists_fixedPoint
    (C : FinitePlusTailLipschitzCertificate n α) :
    ∃ p : FinitePlusTailState n α, C.map p = p :=
  ⟨C.fixedPoint, C.fixedPoint_isFixed⟩


theorem exists_unique_fixedPoint
    (C : FinitePlusTailLipschitzCertificate n α) :
    ∃! p : FinitePlusTailState n α, C.map p = p := by
  refine ⟨C.fixedPoint, C.fixedPoint_isFixed, ?_⟩
  intro y hy
  exact C.eq_fixedPoint_of_isFixed hy


theorem iterate_eq_of_fixed
    (C : FinitePlusTailLipschitzCertificate n α)
    {x : FinitePlusTailState n α} (hx : C.map x = x) (k : ℕ) :
    C.iterate k x = x := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, ih, hx]


theorem iterate_dist_le_pow_mul_of_fixed
    (C : FinitePlusTailLipschitzCertificate n α)
    {p : FinitePlusTailState n α} (hp : C.map p = p)
    (x : FinitePlusTailState n α) (k : ℕ) :
    (C.iterate k x).dist p ≤ C.c ^ k * x.dist p := by
  simpa [C.iterate_eq_of_fixed hp k] using C.iterate_contracts k x p


theorem iterate_dist_le_pow_mul_fixedPoint
    (C : FinitePlusTailLipschitzCertificate n α)
    (x : FinitePlusTailState n α) (k : ℕ) :
    (C.iterate k x).dist C.fixedPoint ≤
      C.c ^ k * x.dist C.fixedPoint :=
  C.iterate_dist_le_pow_mul_of_fixed C.fixedPoint_isFixed x k


theorem fixedPoint_mem_closedBall_of_residual
    (C : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hresidual : (C.map center).dist center ≤ residual)
    (hradius : residual + C.c * radius ≤ radius) :
    FinitePlusTailState.ClosedBall center radius C.fixedPoint := by
  unfold FinitePlusTailState.ClosedBall
  have hd :
      C.fixedPoint.dist center ≤
        C.c * C.fixedPoint.dist center + residual := by
    calc
      C.fixedPoint.dist center =
          (C.map C.fixedPoint).dist center := by
        rw [C.fixedPoint_isFixed]
      _ ≤
          (C.map C.fixedPoint).dist (C.map center) +
            (C.map center).dist center :=
        FinitePlusTailState.dist_triangle
          (C.map C.fixedPoint) (C.map center) center
      _ ≤ C.c * C.fixedPoint.dist center + residual := by
        exact add_le_add (C.mixed_lipschitz C.fixedPoint center) hresidual
  nlinarith [hd, hradius, C.c_lt_one]


theorem exists_fixedPoint_mem_closedBall_of_residual
    (C : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hresidual : (C.map center).dist center ≤ residual)
    (hradius : residual + C.c * radius ≤ radius) :
    ∃ p : FinitePlusTailState n α,
      C.map p = p ∧ FinitePlusTailState.ClosedBall center radius p :=
  ⟨C.fixedPoint, C.fixedPoint_isFixed,
    C.fixedPoint_mem_closedBall_of_residual center hresidual hradius⟩


end FinitePlusTailLipschitzCertificate
end Exact3D
end StatMech
