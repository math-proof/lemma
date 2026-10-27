import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


/--
[AlgHom_injective_of_trdeg_le_one_of_exists_transcendental](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_injective_of_trdeg_le_one_of_exists_transcendental.lean)
-/

private lemma exists_mem_ne_zero_map_eq_zero
  {k D E : Type*}
  [Field k]
  [CommRing D]
  [IsDomain D]
  [Algebra k D]
  [CommRing E]
  [Algebra k E]
  (Ψ : D →ₐ[k] E) (A : Subalgebra k D) (b : D) (hb : Ψ b = 0) (hb0 : b ≠ 0) :
  ∀ (n : ℕ) (P : Polynomial A), P.natDegree = n → P ≠ 0 → Polynomial.aeval b P = 0 →
    ∃ c : A, c ≠ 0 ∧ Ψ c = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hn hP0 hP
    have hsplit : Polynomial.aeval b P = b * Polynomial.aeval b P.divX + algebraMap A D (P.coeff 0) := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add P]
      rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    if h0 : P.coeff 0 = 0 then
      apply ih _ _ P.divX rfl _ _
      ·
        rw [← hn, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
        have : P.natDegree ≠ 0 := by
          intro hz
          apply hP0
          rw [Polynomial.eq_C_of_natDegree_eq_zero hz, h0, map_zero]
        omega
      ·
        intro h
        apply hP0
        rw [← Polynomial.X_mul_divX_add P, h, h0]; simp
      ·
        rw [hP, h0, map_zero, add_zero] at hsplit
        exact (mul_eq_zero.mp hsplit.symm).resolve_left hb0
    else
      refine ⟨P.coeff 0, h0, ?_⟩
      have := congrArg Ψ hsplit
      rwa [hP, map_zero, map_add, map_mul, hb, zero_mul, zero_add, eq_comm] at this

private lemma injective_of_trdeg_le_one_of_transcendental
  {k D L E : Type*}
  [Field k]
  [CommRing D]
  [IsDomain D]
  [Algebra k D]
  [CommRing L]
  [IsDomain L]
  [Algebra k L]
  [CommRing E]
  [Algebra k E]
  (Θ : D →ₐ[k] L) (hΘ : Function.Injective Θ) (hL : Algebra.trdeg k L ≤ 1)
  (Ψ : D →ₐ[k] E) (d : D) (hd : Transcendental k (Ψ d)) : Function.Injective Ψ := by
  classical
  rw [injective_iff_map_eq_zero]
  intro b hb
  by_contra hb0
  have hdT : Transcendental k d := fun halg => hd (halg.algHom Ψ)
  have hx : AlgebraicIndependent k (fun _ : Unit => d) :=
    algebraicIndependent_unique_type_iff.mpr hdT
  have hdep : ¬ AlgebraicIndependent k (fun o : Option Unit => o.elim b (fun _ : Unit => d)) := by
    intro hind
    have h2 := (hind.map' hΘ).lift_cardinalMk_le_trdeg
    have hmk : Cardinal.lift (Cardinal.mk (Option Unit)) = 2 := by
      rw [Cardinal.mk_option, Cardinal.mk_fintype, Fintype.card_unit, Nat.cast_one,
        one_add_one_eq_two, Cardinal.lift_two]
    have h1 := (Cardinal.lift_le (a := Algebra.trdeg k L) (b := (1 : Cardinal))).mpr hL
    have h3 : (2 : Cardinal) ≤ Cardinal.lift (1 : Cardinal) := by
      rw [← hmk]
      exact h2.trans h1
    rw [Cardinal.lift_one] at h3
    norm_num at h3
  rw [hx.option_iff_transcendental] at hdep
  have halg : IsAlgebraic (Algebra.adjoin k (Set.range fun _ : Unit => d)) b := by
    unfold Transcendental at hdep; push Not at hdep; exact hdep
  obtain ⟨P, hP0, hP⟩ := halg
  obtain ⟨c, hc0, hc⟩ :=
    exists_mem_ne_zero_map_eq_zero Ψ (A := Algebra.adjoin k (Set.range fun _ : Unit => d))
      b hb hb0 _ P rfl hP0 hP
  have hrange : (Set.range fun _ : Unit => d) = {d} := by
    ext x; simp [eq_comm]
  have hcmem : (c : D) ∈ Algebra.adjoin k ({d} : Set D) := hrange ▸ c.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hcmem
  obtain ⟨G, hG⟩ := hcmem
  have hG0 : G ≠ 0 := by
    intro h
    apply hc0
    apply Subtype.ext
    change (c : D) = 0
    rw [← hG, h, map_zero]
  apply hd
  refine ⟨G, hG0, ?_⟩
  rw [Polynomial.aeval_algHom_apply]
  change Ψ ((Polynomial.aeval d).toRingHom G) = 0
  rw [hG, hc]

@[path]
private lemma main
  [Field k] [CommRing D] [IsDomain D] [Algebra k D] [CommRing L] [IsDomain L] [Algebra k L] [CommRing E] [Algebra k E]
  {Θ : D →ₐ[k] L}
  {Ψ : D →ₐ[k] E}
-- given
  (hΘ : Function.Injective Θ)
  (hL : Algebra.trdeg k L ≤ 1)
  (hΨ : ∃ d : D, Transcendental k (Ψ d)) :
-- imply
  Function.Injective Ψ := by
-- proof
  obtain ⟨d, hd⟩ := hΨ
  exact injective_of_trdeg_le_one_of_transcendental Θ hΘ hL Ψ d hd


-- created on 2026-10-10
