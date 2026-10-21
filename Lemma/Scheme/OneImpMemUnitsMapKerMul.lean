import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma unitsMap_eq_one_iff_of_eq
  {M a b : ℕ}
  (u : (ZMod M)ˣ)
  -- given
  (hab : a = b)
  (ha : a ∣ M)
  (hb : b ∣ M) :
  -- imply
  ZMod.unitsMap ha u = 1 ↔ ZMod.unitsMap hb u = 1 := by
  -- proof
  subst hab
  rfl

/--
[ModularCurve_unitsMap_div_eq_one_imp_mem_unitsMap_ker_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_unitsMap_div_eq_one_imp_mem_unitsMap_ker_mul.lean)
-/
@[path]
private lemma main
  (q M₀ : ℕ) [Fact q.Prime] [NeZero M₀]
  (u : (ZMod (M₀ * q))ˣ)
  -- given
  (hpM : q ∣ M₀ * q)
  (hu : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1) :
  -- imply
  u ∈ (ZMod.unitsMap (dvd_mul_right M₀ q)).ker := by
  -- proof
  rw [MonoidHom.mem_ker]
  apply (unitsMap_eq_one_iff_of_eq u (Nat.mul_div_cancel M₀ (Fact.out : q.Prime).pos) _ _).mp hu


-- created on 2026-10-20
