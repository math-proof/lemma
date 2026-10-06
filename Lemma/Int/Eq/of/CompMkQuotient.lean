import Mathlib
import sympy.Basic


/--
[Algebra_FormallyUnramified_ext_of_isHausdorff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallyUnramified_ext_of_isHausdorff.lean)
-/
@[main]
private lemma main
  {R A B : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Algebra.FormallyUnramified R A]
  {I : Ideal B} [IsHausdorff I B]
  {f g : A →ₐ[R] B}
-- given
  (h : (Ideal.Quotient.mkₐ R I).comp f = (Ideal.Quotient.mkₐ R I).comp g) :
-- imply
  f = g := by
-- proof
  apply AlgHom.ext
  intro a
  have key : ∀ n : ℕ, f a - g a ∈ I ^ n := by
    intro n
    rcases n with _ | n
    · simp
    · let J : Ideal (B ⧸ I ^ (n+1)) := I.map (Ideal.Quotient.mk (I ^ (n+1)))
      have hJb : J ^ (n+1) = ⊥ := by
        rw [← Ideal.map_pow, Ideal.map_quotient_self]
      have hJ : IsNilpotent J := ⟨n+1, hJb.trans Submodule.zero_eq_bot.symm⟩
      have hn : (Ideal.Quotient.mkₐ R (I ^ (n+1))).comp f
          = (Ideal.Quotient.mkₐ R (I ^ (n+1))).comp g := by
        apply Algebra.FormallyUnramified.lift_unique J hJ
        apply AlgHom.ext
        intro x
        have hx := AlgHom.congr_fun h x
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at hx ⊢
        rw [Ideal.Quotient.eq] at hx ⊢
        rw [← map_sub]
        exact Ideal.mem_map_of_mem _ hx
      have := AlgHom.congr_fun hn a
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      exact (Ideal.Quotient.eq).mp this
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := I) (M := B) (f a - g a) fun n => ?_)
  rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
  exact key n


-- created on 2026-10-05
