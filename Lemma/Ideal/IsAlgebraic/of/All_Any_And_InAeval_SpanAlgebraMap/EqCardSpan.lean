import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[Algebra_isAlgebraic_zmod_quotient_of_card_quotient_eq_of_forall_exists_monic_aeval_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_isAlgebraic_zmod_quotient_of_card_quotient_eq_of_forall_exists_monic_aeval_mem.lean)
-/
@[path]
private lemma main
  {r : ℕ} [Fact r.Prime]
  {𝒪 : Type} [CommRing 𝒪]
  {π : 𝒪}
  {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] [CharP (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r]
-- given
  (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
  (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪,
    p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
-- imply
  let _ : Algebra (ZMod r) (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) :=
    (ZMod.castHom (dvd_refl r) (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})).toAlgebra
  Algebra.IsAlgebraic (ZMod r) (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) := by
-- proof
  classical
  let _ : Algebra (ZMod r) (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) :=
    (ZMod.castHom (dvd_refl r) (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})).toAlgebra
  have hr : r.Prime := Fact.out
  let ψ : 𝒪 →+* Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π} :=
    (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})).comp (algebraMap 𝒪 Onr)
  have hψπ : ∀ a ∈ Ideal.span {π}, ψ a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    show (Ideal.Quotient.mk _) (algebraMap 𝒪 Onr (π * b)) = 0
    rw [map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  let ψbar : 𝒪 ⧸ Ideal.span {π} →+* Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π} :=
    Ideal.Quotient.lift (Ideal.span {π}) ψ hψπ
  let _ : Finite (𝒪 ⧸ Ideal.span {π}) := Nat.finite_of_card_ne_zero (by rw [hres]; apply hr.ne_zero)
  let _ : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hcard : Fintype.card (𝒪 ⧸ Ideal.span {π}) = r := by
    rw [← Nat.card_eq_fintype_card]
    apply hres
  let e : ZMod r ≃+* 𝒪 ⧸ Ideal.span {π} := ZMod.ringEquivOfPrime _ hr hcard
  have hψbar : ψbar.comp e.toRingHom = algebraMap (ZMod r) (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) :=
    Subsingleton.elim _ _
  let χ : 𝒪 →+* ZMod r := e.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {π}))
  have hχ : (algebraMap (ZMod r) (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})).comp χ = ψ := by
    rw [← hψbar]
    ext a
    show ψbar (e (e.symm (Ideal.Quotient.mk (Ideal.span {π}) a))) = ψ a
    rw [RingEquiv.apply_symm_apply]
    rfl
  refine ⟨fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p, hp, hpx⟩ := hOnr_alg x
  refine ⟨p.map χ, (hp.map χ).ne_zero, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hχ]
  have h := Polynomial.hom_eval₂ p (algebraMap 𝒪 Onr) (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) x
  rw [← Polynomial.aeval_def] at h
  rw [← h, Ideal.Quotient.eq_zero_iff_mem]
  apply hpx


-- created on 2026-10-13
