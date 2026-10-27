import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[IsIntegral_of_forall_isPrime_isIntegral_quotient_mk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsIntegral_of_forall_isPrime_isIntegral_quotient_mk.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  (a : A)
  -- given
  (h : ∀ (p : Ideal A), p.IsPrime → IsIntegral R (Ideal.Quotient.mk p a)) :
  -- imply
  IsIntegral R a := by
  -- proof
  classical
  let T : Submonoid A :=
    { carrier := {x | ∃ p : Polynomial R, p.Monic ∧ Polynomial.aeval a p = x}
      one_mem' := ⟨1, Polynomial.monic_one, by simp⟩
      mul_mem' := by
        rintro x y ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
        refine ⟨p * q, hp.mul hq, by simp⟩ }
  by_contra hnot
  have hdisj : Disjoint ((nilradical A : Ideal A) : Set A) (T : Set A) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, mem_nilradical] at hx
    obtain ⟨n, hn⟩ := hx
    apply hnot
    obtain h0 | hpos := Nat.eq_zero_or_pos n
    ·
      rw [h0, pow_zero] at hn
      let _ : Subsingleton A := subsingleton_of_zero_eq_one hn.symm
      refine ⟨Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
    ·
      refine ⟨p ^ n, hp.pow n, ?_⟩
      rw [← Polynomial.aeval_def, map_pow, hn]
  obtain ⟨P, hP, -, hPT⟩ := Ideal.exists_le_prime_disjoint (nilradical A) T hdisj
  obtain ⟨q, hq, hq0⟩ := h P hP
  have hmem : Polynomial.aeval a q ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Polynomial.aeval (Ideal.Quotient.mk P a) q = Ideal.Quotient.mkₐ R P (Polynomial.aeval a q) := by
      rw [← Polynomial.aeval_algHom_apply]
      rfl
    rw [← Polynomial.aeval_def] at hq0
    rw [← Ideal.Quotient.mkₐ_eq_mk R, ← this, hq0]
  refine Set.disjoint_left.mp hPT hmem ⟨q, hq, rfl⟩


-- created on 2026-10-20
