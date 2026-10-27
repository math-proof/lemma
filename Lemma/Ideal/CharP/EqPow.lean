import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false


/--
[CerednikDrinfeld_FormalOmega_charP_residue_and_forall_exists_pow_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_FormalOmega_charP_residue_and_forall_exists_pow_eq.lean)
-/
@[path]
private lemma main
  {r : ℕ} [Fact r.Prime]
  (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
  (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
  (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
  (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
  (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
  (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
  (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
  (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
  -- imply
  CharP (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r ∧ ∀ a : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}, ∃ b : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}, b ^ r = a := by
  -- proof
  classical
  let hmaxI : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal := hOnr_max
  let _ : Nontrivial (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) := Ideal.Quotient.nontrivial_iff.mpr hOnr_max.ne_top
  refine ⟨?_, ?_⟩
  ·
    refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
    have hr : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by
      rw [← hunr]
      apply Ideal.subset_span (Set.mem_singleton ((r : ℕ) : 𝒪))
    have hmem : ((r : ℕ) : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
      have hmap : algebraMap 𝒪 Onr (c * π) = ((r : ℕ) : Onr) := by
        rw [hc, map_natCast]
      rw [← hmap, map_mul]
      apply Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton (algebraMap 𝒪 Onr π)))
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})), Ideal.Quotient.eq_zero_iff_mem]
    apply hmem
  ·
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hr0 : r ≠ 0 := (Fact.out : r.Prime).ne_zero
    have hmonic : (Polynomial.X ^ r - Polynomial.C x : Polynomial Onr).Monic := Polynomial.monic_X_pow_sub_C x hr0
    have hdeg : 0 < (Polynomial.X ^ r - Polynomial.C x : Polynomial Onr).natDegree := by
      rw [Polynomial.natDegree_X_pow_sub_C]
      apply (Fact.out : r.Prime).pos
    obtain ⟨y, hy⟩ := hOnr_closed _ hmonic hdeg
    refine ⟨Ideal.Quotient.mk _ y, ?_⟩
    rw [← map_pow, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using hy


-- created on 2026-10-20
