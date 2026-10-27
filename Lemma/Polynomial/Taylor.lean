import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


/--
[existsUnique_taylor_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/Taylor.lean)
-/
@[path]
private lemma existsUnique_taylor_remainder_eq
  [CommRing k]
-- given
  (f : k[X]) (a : k) :
-- imply
  ∃! g : k[X],
    f = C (f.eval a) + C (f.derivative.eval a) * (X - C a) +
      g * (X - C a) ^ 2 := by
-- proof
  obtain ⟨q₁, hq₁⟩ := X_sub_C_dvd_sub_C_eval (a := a) (p := f)
  obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (a := a) (p := q₁)
  have hdecomp : f = C (f.eval a) + (X - C a) * q₁ := by
    linear_combination hq₁
  have hder : f.derivative = q₁ + (X - C a) * q₁.derivative := by
    have hcalc : (C (f.eval a) + (X - C a) * q₁).derivative =
        q₁ + (X - C a) * q₁.derivative := by
      rw [derivative_add, derivative_C, zero_add, derivative_mul,
        derivative_X_sub_C, one_mul]
    rwa [← hdecomp] at hcalc
  have hderiv : q₁.eval a = f.derivative.eval a := by
    have h := congrArg (eval a) hder
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
      add_zero] at h
    exact h.symm
  have hq₂eq : q₁ = C (f.derivative.eval a) + (X - C a) * g := by
    rw [← hderiv]
    linear_combination hg
  have key : f = C (f.eval a) + C (f.derivative.eval a) * (X - C a) +
      g * (X - C a) ^ 2 := calc
      _ = C (f.eval a) + (X - C a) * q₁ := hdecomp
      _ = C (f.eval a) + C (f.derivative.eval a) * (X - C a) +
          g * (X - C a) ^ 2 := by
        rw [hq₂eq]
        ring
  refine ⟨g, key, ?_⟩
  intro y hy
  have hcancel : (y - g) * (X - C a) ^ 2 = 0 := by
    linear_combination key - hy
  apply sub_eq_zero.mp
  apply ((monic_X_sub_C a).pow 2).mul_left_eq_zero_iff.mp
  exact hcancel


-- created on 2026-10-09
