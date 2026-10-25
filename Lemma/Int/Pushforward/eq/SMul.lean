import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.DivisorPushPull
import Lemma.Int.P2MUtil
open AlgebraicCurve
open AlgebraicCurve.Divisor


private lemma pushforward_pullback_single
  {K F F' : Type*}
  [Field K]
  [Field F]
  [Field F']
  [Algebra K F]
  [Algebra K F']
  [Algebra F F']
  [IsScalarTower K F F']
  [Algebra.IsIntegral F F']
  [HasPrincipalDivisors K F']
  (v : Place K F) (n : ℤ) :
  pushforward F (pullback F' (Finsupp.single v n)) = Finsupp.single v
    (n * ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
  rw [pullback_single, map_sum]
  calc
    _ = ∑ w ∈ v.fiber F',
            Finsupp.single v (n * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ))) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [pushforward_single, Place.mem_fiber.mp hw, mul_assoc]
    _ = Finsupp.single v (∑ w ∈ v.fiber F', n * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ))) :=
      (Finsupp.single_finsetSum _ _ _).symm
    _ = Finsupp.single v (n * ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
      rw [← Finset.mul_sum]

private lemma pushforward_pullback_apply
  {K F F' : Type*}
  [Field K]
  [Field F]
  [Field F']
  [Algebra K F]
  [Algebra K F']
  [Algebra F F']
  [IsScalarTower K F F']
  [Algebra.IsIntegral F F']
  [HasPrincipalDivisors K F']
  (D : Divisor K F) (v : Place K F) :
  pushforward F (pullback F' D) v = (∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) * D v := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add u n D _ _ ih =>
    rw [map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, ih,
      pushforward_pullback_single, mul_add]
    congr 1
    if huv : u = v then
      subst huv
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same, mul_comm]
    else
      rw [Finsupp.single_eq_of_ne (Ne.symm huv), Finsupp.single_eq_of_ne (Ne.symm huv),
        mul_zero]

private lemma pushforward_pullback_of_sumRam
  {K F F' : Type*}
  [Field K]
  [Field F]
  [Field F']
  [Algebra K F]
  [Algebra K F']
  [Algebra F F']
  [IsScalarTower K F F']
  [Algebra.IsIntegral F F']
  [HasPrincipalDivisors K F']
  [SumRamificationInertia K F F'] (D : Divisor K F) :
  pushforward F (pullback F' D) = (Module.finrank F F' : ℤ) • D := by
  ext v
  rw [pushforward_pullback_apply,
    SumRamificationInertia.sum_ramificationIndex_mul_inertiaDeg (F' := F') v,
    Finsupp.smul_apply, smul_eq_mul]
/--
[AlgebraicCurve_Divisor_pushforward_pullback_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Divisor_pushforward_pullback_of_finite.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [Module.Finite F F'] [SumRamificationInertia K F F']
  {D : Divisor K F} :
-- imply
  Divisor.pushforward F (Divisor.pullback F' D) = (Module.finrank F F' : ℤ) • D :=
-- proof
  pushforward_pullback_of_sumRam D


-- created on 2026-10-24
