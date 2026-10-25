import Mathlib
import sympy.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticCapacity
open DifferentialFormSpace


/--
[SymplecticCapacity.cap_eq_ball_capacity_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticCapacity.lean)
-/
@[path]
lemma SymplecticCapacity.cap_eq_ball_capacity_val
  {Ω : ℕ → Type*}
  [DifferentialFormSpace Ω VF]
  {c : SymplecticCapacity Ω VF}
  {S : SymplecticManifold Ω VF}
  [hBall : IsSymplecticBall S] :
-- imply
  c.cap S = hBall.capacity_val := by
-- proof
  rw [hBall.capacity_eq]
  exact c.normalization_ball S

/--
[SymplecticCapacity.cap_eq_cylinder_capacity_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticCapacity.lean)
-/
@[path]
lemma SymplecticCapacity.cap_eq_cylinder_capacity_val
  {Ω : ℕ → Type*}
  [DifferentialFormSpace Ω VF]
  {c : SymplecticCapacity Ω VF}
  {S : SymplecticManifold Ω VF}
  [hCyl : IsSymplecticCylinder S] :
-- imply
  c.cap S = hCyl.capacity_val := by
-- proof
  rw [hCyl.capacity_eq]
  exact c.normalization_cylinder S

/--
[SymplecticCapacity.cap_ball_eq_pi_rsq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticCapacity.lean)
-/
@[path]
lemma SymplecticCapacity.cap_ball_eq_pi_rsq
  {Ω : ℕ → Type*}
  [DifferentialFormSpace Ω VF]
  {c : SymplecticCapacity Ω VF}
  {S : SymplecticManifold Ω VF}
  [hBall : IsSymplecticBall S] :
-- imply
  (c.cap S : ℝ) = Real.pi * hBall.radius ^ 2 := by
-- proof
  have h := c.normalization_ball S
  rw [h]
  rfl

/--
[SymplecticCapacity.cap_cylinder_eq_pi_rsq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticCapacity.lean)
-/
@[path]
lemma SymplecticCapacity.cap_cylinder_eq_pi_rsq
  {Ω : ℕ → Type*}
  [DifferentialFormSpace Ω VF]
  {c : SymplecticCapacity Ω VF}
  {S : SymplecticManifold Ω VF}
  [hCyl : IsSymplecticCylinder S] :
-- imply
  (c.cap S : ℝ) = Real.pi * hCyl.radius ^ 2 := by
-- proof
  have h := c.normalization_cylinder S
  rw [h]
  rfl


-- created on 2026-10-23
