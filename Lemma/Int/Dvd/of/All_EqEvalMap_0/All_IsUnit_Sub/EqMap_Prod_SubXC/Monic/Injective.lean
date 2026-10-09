import Mathlib
import sympy.Basic


/--
[Polynomial_dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_dvd_of_monic_of_map_eq_prod_X_sub_C_of_forall_eval_eq_zero.lean)
-/
@[path]
private lemma main
  [Fintype ι] [DecidableEq ι]
  {T : Type u} [CommRing T]
  {S : Type v} [CommRing S]
  {f : T →+* S}
  {r : ι → S}
  {F : Polynomial T}
-- given
  (hf : Function.Injective f)
  (h : Polynomial T)
  (hh : h.Monic)
  (hsplit : h.map f = ∏ i, (Polynomial.X - Polynomial.C (r i)))
  (hsep : ∀ i j, i ≠ j → IsUnit (r i - r j))
  (hF : ∀ i, (F.map f).eval (r i) = 0) :
-- imply
  h ∣ F := by
-- proof
  classical

  have hdvdS : h.map f ∣ F.map f := by
    rw [hsplit]
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (hsep i j hij)
    · intro i _
      exact Polynomial.dvd_iff_isRoot.mpr (hF i)

  have hR : F %ₘ h = 0 := by
    apply Polynomial.map_injective f hf
    rw [Polynomial.map_modByMonic f hh, Polynomial.map_zero]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd (hh.map f)).mpr hdvdS
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hh).mp hR


-- created on 2026-10-05
