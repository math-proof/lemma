import Mathlib
import sympy.Basic
open Module Submodule


private lemma valuation_units
  {p : ℕ}
  [Fact p.Prime]
  (u : ℤ_[p]ˣ) : (u : ℤ_[p]).valuation = 0 := by
  have h := PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero u⁻¹)
  rw [Units.mul_inv, PadicInt.valuation_one] at h
  omega

private lemma valuation_prod
  {p : ℕ}
  [Fact p.Prime]
  {ι : Type*} (s : Finset ι) (a : ι → ℤ_[p]) (ha : ∀ i ∈ s, a i ≠ 0) :
  (∏ i ∈ s, a i).valuation = ∑ i ∈ s, (a i).valuation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      PadicInt.valuation_mul (ha j (Finset.mem_insert_self j s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => ha i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => ha i (Finset.mem_insert_of_mem hi)]

private lemma natCard_quotient_span_singleton
  {p : ℕ}
  [Fact p.Prime]
  (a : ℤ_[p]) (ha : a ≠ 0) :
  Nat.card (ℤ_[p] ⧸ Ideal.span ({a} : Set ℤ_[p])) = p ^ a.valuation := by
  have hspan : Ideal.span ({a} : Set ℤ_[p]) = Ideal.span {(p : ℤ_[p]) ^ a.valuation} := by
    rw [Ideal.span_singleton_eq_span_singleton]
    refine ⟨(PadicInt.unitCoeff ha)⁻¹, ?_⟩
    rw [Units.mul_inv_eq_iff_eq_mul, mul_comm]
    exact PadicInt.unitCoeff_spec ha
  rw [hspan, ← PadicInt.ker_toZModPow,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) a.valuation))).toEquiv,
    Nat.card_zmod]

set_option maxHeartbeats 999999 in

private lemma helper_main (p : ℕ) [Fact p.Prime]
  {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
  (f : Module.End ℤ_[p] T) (hf : LinearMap.det f ≠ 0) :
  Nat.card (T ⧸ LinearMap.range f) = p ^ (LinearMap.det f).valuation := by
  classical
  let b := Module.Free.chooseBasis ℤ_[p] T
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hker
    exact hf (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
  let e : T ≃ₗ[ℤ_[p]] LinearMap.range f := LinearEquiv.ofInjective f hinj
  have h : Module.finrank ℤ_[p] (LinearMap.range f) = Module.finrank ℤ_[p] T :=
    e.symm.finrank_eq
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  have ha0 : ∀ i, a i ≠ 0 := smithNormalFormCoeffs_ne_zero b h
  let e' : T ≃ₗ[ℤ_[p]] LinearMap.range f := b'.equiv ab (Equiv.refl _)
  let g : T →ₗ[ℤ_[p]] T := (LinearMap.range f).subtype ∘ₗ (e' : T →ₗ[ℤ_[p]] LinearMap.range f)
  have g_apply : ∀ x, g x = b'.equiv ab (Equiv.refl _) x := fun x => rfl
  have hfe : f = (LinearMap.range f).subtype ∘ₗ (e : T →ₗ[ℤ_[p]] LinearMap.range f) := by
    ext x
    rfl
  have hfg : Associated (LinearMap.det f) (LinearMap.det g) := by
    rw [hfe]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have hga : ∀ i, g (b' i) = a i • b' i := by
    intro i
    rw [g_apply, b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdetg : LinearMap.det g = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have hmat : LinearMap.toMatrix b' b' g = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hga, map_smul, Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one]
      if hij : i = j then
        rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
      else
        rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [hmat, Matrix.det_diagonal]
  have hval : (LinearMap.det f).valuation = ∑ i, (a i).valuation := by
    obtain ⟨u, hu⟩ := hfg
    have h1 : (LinearMap.det g).valuation = (LinearMap.det f).valuation := by
      rw [← hu, PadicInt.valuation_mul hf (Units.ne_zero u), valuation_units, add_zero]
    rw [← h1, hdetg, valuation_prod _ _ fun i _ => ha0 i]
  rw [Nat.card_congr ((LinearMap.range f).quotientEquivPiSpan b h).toEquiv, Nat.card_pi, hval,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact natCard_quotient_span_singleton (a i) (ha0 i)
/--
[PadicInt_natCard_quotient_range_eq_pow_valuation_det](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PadicInt_natCard_quotient_range_eq_pow_valuation_det.lean)
-/
@[path]
private lemma main
  [AddCommGroup T]
  {p : ℕ} [Fact p.Prime] [Module ℤ_[p] T] [Module.Free ℤ_[p] T] [Module.Finite ℤ_[p] T]
  {f : Module.End ℤ_[p] T}
-- given
  (hf : LinearMap.det f ≠ 0) :
-- imply
  Nat.card (T ⧸ LinearMap.range f) = p ^ (LinearMap.det f).valuation :=
-- proof
  helper_main p f hf


-- created on 2026-10-23
