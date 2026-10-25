/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part2


namespace StatMech

namespace Exact3D

open scoped NNReal


namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type*}


theorem fixedPoint_isFixed
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    C.contraction.map C.fixedPoint = C.fixedPoint :=
  C.contraction.fixedPoint_isFixed


theorem fixedPoint_mem
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    FinitePlusTailState.ClosedBall C.center C.radius C.fixedPoint :=
  C.contraction.fixedPoint_mem_closedBall_of_residual
    C.center C.residual_bound C.residual_plus_mul_le_radius


theorem fixedPoint_mem_selected
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    FinitePlusTailState.ClosedBall C.center C.radius C.fixedPoint :=
  C.fixedPoint_mem


theorem fixedPoint_mem_of_radius_le
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    FinitePlusTailState.ClosedBall C.center radius' C.fixedPoint :=
  FinitePlusTailState.closedBall_mono_radius C.fixedPoint_mem hradius


theorem fixedPoint_unique
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {x y : FinitePlusTailState n α}
    (hx : C.contraction.map x = x) (hy : C.contraction.map y = y) :
    x = y :=
  C.contraction.fixedPoint_unique hx hy


theorem eq_fixedPoint_of_isFixed
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {x : FinitePlusTailState n α} (hx : C.contraction.map x = x) :
    x = C.fixedPoint :=
  C.contraction.eq_fixedPoint_of_isFixed hx


@[simp] theorem ofFiniteClosedBall_fixedPoint_eq_ofFinite
    {finiteMap : (Fin n → ℝ) → Fin n → ℝ}
    (C : FiniteContraction.ClosedBallContractionCertificate finiteMap) :
    (ofFiniteClosedBall (α := α) C).fixedPoint =
      FinitePlusTailState.ofFinite (α := α) C.fixedPoint := by
  symm
  apply (ofFiniteClosedBall (α := α) C).eq_fixedPoint_of_isFixed
  change
    (FinitePlusTailLipschitzCertificate.ofFiniteMap
      (α := α) finiteMap C.c_nonneg C.c_lt_one C.lipschitz).map
      (FinitePlusTailState.ofFinite C.fixedPoint) =
        FinitePlusTailState.ofFinite C.fixedPoint
  rw [FinitePlusTailLipschitzCertificate.ofFiniteMap_map_ofFinite]
  rw [C.fixedPoint_isFixed]


theorem exists_fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    ∃ p : FinitePlusTailState n α,
      C.contraction.map p = p ∧
        FinitePlusTailState.ClosedBall C.center C.radius p :=
  ⟨C.fixedPoint, C.fixedPoint_isFixed, C.fixedPoint_mem⟩


theorem exists_unique_fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    ∃! p : FinitePlusTailState n α, C.contraction.map p = p :=
  C.contraction.exists_unique_fixedPoint


theorem iterate_mem
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {x : FinitePlusTailState n α}
    (hx : FinitePlusTailState.ClosedBall C.center C.radius x) (k : ℕ) :
    FinitePlusTailState.ClosedBall C.center C.radius
      (C.contraction.iterate k x) :=
  C.contraction.mapsClosedBall_iterate_mem C.mapsClosedBall hx k


theorem iterate_dist_le_pow_mul_of_fixed
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {p : FinitePlusTailState n α}
    (hp : C.contraction.map p = p)
    (x : FinitePlusTailState n α) (k : ℕ) :
    (C.contraction.iterate k x).dist p ≤
      C.contraction.c ^ k * x.dist p :=
  C.contraction.iterate_dist_le_pow_mul_of_fixed hp x k


theorem iterate_dist_le_pow_mul_fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (x : FinitePlusTailState n α) (k : ℕ) :
    (C.contraction.iterate k x).dist C.fixedPoint ≤
      C.contraction.c ^ k * x.dist C.fixedPoint :=
  C.contraction.iterate_dist_le_pow_mul_fixedPoint x k


theorem residual_le_margin
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    C.residual ≤ (1 - C.contraction.c) * C.radius := by
  nlinarith [C.radius_bound]


end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
