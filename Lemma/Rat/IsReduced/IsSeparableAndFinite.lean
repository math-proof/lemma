import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial
open scoped TensorProduct


attribute [local instance] Ideal.Quotient.field


private lemma isSeparable_of_finite_of_isReduced_of_formallyUnramified
  [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] [_root_.IsReduced A]
  [Algebra.FormallyUnramified E A] :
-- imply
  Algebra.IsSeparable E A := by
-- proof
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite E A
  rw [Algebra.isSeparable_iff]
  intro x
  refine ⟨IsIntegral.of_finite E x, ?_⟩
  have hMfin : {I : Ideal A | I.IsMaximal}.Finite := IsArtinianRing.setOfPred_isMaximal_finite A
  let p : Ideal A → E[X] := fun I => minpoly E (Ideal.Quotient.mkₐ E I x)
  let s : Finset E[X] := hMfin.toFinset.image p
  have hp : ∀ I : Ideal A, I.IsMaximal → (p I).Monic ∧ Irreducible (p I) ∧ (p I).Separable := by
    intro I hI
    have : I.IsMaximal := hI
    have : Algebra.IsSeparable E (A ⧸ I) :=
      (Algebra.FormallyUnramified.iff_isSeparable E (A ⧸ I)).mp inferInstance
    have hint : IsIntegral E (Ideal.Quotient.mkₐ E I x) := IsIntegral.of_finite E _
    refine ⟨minpoly.monic hint, minpoly.irreducible hint, Algebra.IsSeparable.isSeparable E _⟩
  have hs : ∀ q ∈ s, q.Monic ∧ Irreducible q ∧ q.Separable := by
    intro q hq
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hq
    apply hp I (hMfin.mem_toFinset.mp hI)
  let P : E[X] := ∏ q ∈ s, q
  have hPsep : P.Separable := by
    apply Polynomial.separable_prod'
    ·
      intro q₁ h₁ q₂ h₂ hne
      obtain ⟨hm₁, hi₁, -⟩ := hs q₁ h₁
      obtain ⟨hm₂, hi₂, -⟩ := hs q₂ h₂
      rw [hi₁.coprime_iff_not_dvd]
      intro hdvd
      apply hne (Polynomial.eq_of_monic_of_associated hm₁ hm₂ (hi₁.associated_of_dvd hi₂ hdvd))
    ·
      intro q hq
      apply (hs q hq).2.2
  have hdvdAll : ∀ I : Ideal A, I.IsMaximal → p I ∣ P := fun I hI =>
    Finset.dvd_prod_of_mem _ (Finset.mem_image.mpr ⟨I, hMfin.mem_toFinset.mpr hI, rfl⟩)
  clear_value P
  have hmem : ∀ I : Ideal A, I.IsMaximal → aeval x P ∈ I := by
    intro I hI
    have h2 : aeval (Ideal.Quotient.mkₐ E I x) P = 0 :=
      Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero (hdvdAll I hI) (minpoly.aeval E _)
    rw [Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    apply Ideal.Quotient.eq_zero_iff_mem.mp h2
  have hjac : aeval x P ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    intro J hJ
    apply hmem J hJ.2
  apply hPsep.of_dvd
  apply minpoly.dvd
  apply IsNilpotent.eq_zero
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  refine ⟨n, ?_⟩
  have : aeval x P ^ n ∈ (⊥ : Ideal A).jacobson ^ n := Ideal.pow_mem_pow hjac n
  rw [hn] at this
  simpa using this


/--
[Algebra_IsSeparable_isReduced_and_isSeparable_and_finite_tensorProduct](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsSeparable_isReduced_and_isSeparable_and_finite_tensorProduct.lean)
-/
@[path]
private lemma main
  [Field K₁] [Field K] [Field E] [Algebra K₁ K] [Algebra K₁ E]
  [FiniteDimensional K₁ K] [Algebra.IsSeparable K₁ K] :
-- imply
  _root_.IsReduced (E ⊗[K₁] K) ∧ Algebra.IsSeparable E (E ⊗[K₁] K) ∧ Module.Finite E (E ⊗[K₁] K) := by
-- proof
  have : Algebra.FormallyUnramified K₁ K := Algebra.FormallyUnramified.of_isSeparable K₁ K
  have hred : _root_.IsReduced (E ⊗[K₁] K) :=
    Algebra.FormallyUnramified.isReduced_of_field E (E ⊗[K₁] K)
  refine ⟨hred, isSeparable_of_finite_of_isReduced_of_formallyUnramified (E := E) (A := E ⊗[K₁] K), inferInstance⟩


-- created on 2026-10-12
