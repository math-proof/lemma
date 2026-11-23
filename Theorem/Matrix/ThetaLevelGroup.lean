module

public import Mathlib
public import Instance.AlgebraicGeometry_ThetaLevelGroup
public import Structure.AlgebraicGeometry_ThetaLevelGroup
public import Abbrev.AlgebraicGeometry_ThetaLevelGroup

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace AlgebraicGeometry.ThetaLevel

section Heis

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ)


public theorem iota_natCast (i : Fin g) (hdiv : δ i ∣ 2 * d) (x : ℕ) :
    iota δ d i (x : ZMod (δ i)) = ((2 * d / δ i : ℕ) : ZMod (2 * d)) * (x : ZMod (2 * d)) := by
  rw [iota, dif_pos hdiv]
  have hx : ((x : ℤ) : ZMod (δ i)) = (x : ZMod (δ i)) := Int.cast_natCast x
  rw [← hx, ZMod.lift_coe]
  change ((2 * d / δ i : ℕ) : ZMod (2 * d)) * ((x : ℤ) : ZMod (2 * d)) = _
  rw [Int.cast_natCast]


public theorem pair_add_left (k k' h : HH δ) : pair δ d (k + k') h = pair δ d k h + pair δ d k' h := by
  simp only [pair, Pi.add_apply, add_mul, map_add, Finset.sum_add_distrib]


public theorem pair_add_right (k h h' : HH δ) : pair δ d k (h + h') = pair δ d k h + pair δ d k h' := by
  simp only [pair, Pi.add_apply, mul_add, map_add, Finset.sum_add_distrib]


public theorem pair_zero_left (h : HH δ) : pair δ d 0 h = 0 := by
  simp [pair]


public theorem pair_zero_right (k : HH δ) : pair δ d k 0 = 0 := by
  simp [pair]


public theorem pair_neg_right (k h : HH δ) : pair δ d k (-h) = -pair δ d k h := by
  simp only [pair, Pi.neg_apply, mul_neg, map_neg, Finset.sum_neg_distrib]


public theorem pair_neg_left (k h : HH δ) : pair δ d (-k) h = -pair δ d k h := by
  simp only [pair, Pi.neg_apply, neg_mul, map_neg, Finset.sum_neg_distrib]


public theorem pair_comm (k h : HH δ) : pair δ d k h = pair δ d h k := by
  simp only [pair, mul_comm]

@[ext]

namespace Heis

variable {δ} {d}


@[simp] public theorem mul_a (z z' : Heis δ d) : (z * z').a = z.a + z'.a + pair δ d z.k z'.h := rfl

@[simp] public theorem mul_h (z z' : Heis δ d) : (z * z').h = z.h + z'.h := rfl

@[simp] public theorem mul_k (z z' : Heis δ d) : (z * z').k = z.k + z'.k := rfl

@[simp] public theorem one_a : (1 : Heis δ d).a = 0 := rfl

@[simp] public theorem one_h : (1 : Heis δ d).h = 0 := rfl

@[simp] public theorem one_k : (1 : Heis δ d).k = 0 := rfl

@[simp] public theorem inv_a (z : Heis δ d) : z⁻¹.a = -z.a + pair δ d z.k z.h := rfl

@[simp] public theorem inv_h (z : Heis δ d) : z⁻¹.h = -z.h := rfl

@[simp] public theorem inv_k (z : Heis δ d) : z⁻¹.k = -z.k := rfl


@[simp] public theorem cen_a (a : ZMod (2 * d)) : (cen a : Heis δ d).a = a := rfl

@[simp] public theorem cen_h (a : ZMod (2 * d)) : (cen a : Heis δ d).h = 0 := rfl

@[simp] public theorem cen_k (a : ZMod (2 * d)) : (cen a : Heis δ d).k = 0 := rfl


public theorem cen_mul (a : ZMod (2 * d)) (z : Heis δ d) : cen a * z = ⟨a + z.a, z.h, z.k⟩ := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, pair_zero_left]


public theorem mul_cen (a : ZMod (2 * d)) (z : Heis δ d) : z * cen a = ⟨z.a + a, z.h, z.k⟩ := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, pair_zero_right]


@[simp] public theorem theta_a (h : HH δ) : (theta h : Heis δ d).a = 0 := rfl

@[simp] public theorem theta_h (h : HH δ) : (theta h : Heis δ d).h = h := rfl

@[simp] public theorem theta_k (h : HH δ) : (theta h : Heis δ d).k = 0 := rfl

@[simp] public theorem eta_a (k : HH δ) : (eta k : Heis δ d).a = 0 := rfl

@[simp] public theorem eta_h (k : HH δ) : (eta k : Heis δ d).h = 0 := rfl

@[simp] public theorem eta_k (k : HH δ) : (eta k : Heis δ d).k = k := rfl


public theorem cen_mul_theta_mul_eta (z : Heis δ d) : cen z.a * theta z.h * eta z.k = z := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, theta, eta, pair_zero_left, pair_zero_right]


public theorem eta_mul_theta (h k : HH δ) : (eta k * theta h : Heis δ d) = cen (pair δ d k h) * theta h * eta k := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, theta, eta, pair_zero_left, pair_zero_right]

variable (δ d) in


public theorem omegaPow_zero : omegaPow d B ω 0 = 1 := by
  simp [omegaPow]


public theorem omegaPow_aux_pow_mod_eq {M : Type} [Monoid M] (x : M) {m : ℕ} (hx : x ^ m = 1) (n : ℕ) :
    x ^ (n % m) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, hx, one_pow, mul_one]


public theorem omegaPow_add (hω : ω ^ (2 * d) = 1) (a b : ZMod (2 * d)) :
    omegaPow d B ω (a + b) = omegaPow d B ω a * omegaPow d B ω b := by
  simp only [omegaPow]
  rw [ZMod.val_add, omegaPow_aux_pow_mod_eq ω hω, pow_add]

omit [NeZero d] in

public theorem omegaPow_natCast (hω : ω ^ (2 * d) = 1) (n : ℕ) :
    omegaPow d B ω (n : ZMod (2 * d)) = ω ^ n := by
  simp only [omegaPow]
  rw [ZMod.val_natCast, omegaPow_aux_pow_mod_eq ω hω]


@[simp] public theorem shiftOp_apply (h : HH δ) (v : HH δ → B) (x : HH δ) : shiftOp δ B h v x = v (x - h) := rfl


@[simp] public theorem diagOp_apply (c : HH δ → B) (v : HH δ → B) (x : HH δ) : diagOp δ B c v x = c x * v x := rfl


public theorem schrod_apply (z : Heis δ d) (v : HH δ → B) (x : HH δ) :
    schrod δ d B ω z v x = omegaPow d B ω z.a * (thetaChar δ d B ω z.k (x - z.h) * v (x - z.h)) := by
  simp [schrod]


public theorem schrod_mul (hω : ω ^ (2 * d) = 1) (z z' : Heis δ d) :
    schrod δ d B ω (z * z') = schrod δ d B ω z ∘ₗ schrod δ d B ω z' := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp only [LinearMap.comp_apply, schrod_apply, Heis.mul_a, Heis.mul_h, Heis.mul_k, thetaChar,
    pair_add_left]
  have hx : x - (z.h + z'.h) = x - z.h - z'.h := by abel
  rw [hx, show pair δ d z.k (x - z.h - z'.h) = pair δ d z.k (x - z.h) + -pair δ d z.k z'.h by
    rw [sub_eq_add_neg (x - z.h), pair_add_right, pair_neg_right]]
  simp only [omegaPow_add d B ω hω]

  have hcancel : omegaPow d B ω (pair δ d z.k z'.h) * omegaPow d B ω (-pair δ d z.k z'.h) = 1 := by
    rw [← omegaPow_add d B ω hω, add_neg_cancel, omegaPow_zero]

  set A := omegaPow d B ω z.a
  set A' := omegaPow d B ω z'.a
  set P := omegaPow d B ω (pair δ d z.k z'.h)
  set Q := omegaPow d B ω (-pair δ d z.k z'.h)
  set R1 := omegaPow d B ω (pair δ d z.k (x - z.h))
  set R2 := omegaPow d B ω (pair δ d z'.k (x - z.h - z'.h))
  set w := v (x - z.h - z'.h)
  calc A * A' * P * (R1 * Q * R2 * w) = (P * Q) * (A * (R1 * (A' * (R2 * w)))) := by ring
    _ = A * (R1 * (A' * (R2 * w))) := by rw [hcancel, one_mul]

omit [NeZero d] in

public theorem schrod_one : schrod δ d B ω 1 = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp [schrod_apply, thetaChar, pair_zero_left, omegaPow_zero]


public theorem schrodMat_apply (z : Heis δ d) (i j : Fin n) :
    schrodMat δ d B ω e z i j = if e i = e j + z.h then omegaPow d B ω (z.a + pair δ d z.k (e j)) else 0 := rfl


public theorem isIntertwiner_inter (γ : MulAut (Heis δ d)) (hU : ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U) :
    IsIntertwiner δ d B ω e γ (inter δ d B ω e γ) := by
  classical
  rw [inter, dif_pos hU]
  exact hU.choose_spec


public theorem inter_of_not_exists (γ : MulAut (Heis δ d)) (hU : ¬ ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U) :
    inter δ d B ω e γ = 1 := by
  classical
  rw [inter, dif_neg hU]

end Matrices

end AlgebraicGeometry.ThetaLevel

end
