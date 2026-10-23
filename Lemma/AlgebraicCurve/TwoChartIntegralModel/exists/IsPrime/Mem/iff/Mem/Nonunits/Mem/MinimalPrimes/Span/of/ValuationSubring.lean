import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open Polynomial


/-- ported from external source -/

private lemma exists_eq_C_mul_of_map_residue_eq_zero {R : Type u} [CommRing R] [IsLocalRing R]
  (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
  (P : R[X]) (hP : P.map (IsLocalRing.residue R) = 0) : ∃ P₁ : R[X], P = C ϖ * P₁ := by
  have h : C ϖ ∣ P := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have hi : (P.map (IsLocalRing.residue R)).coeff i = 0 := by rw [hP, coeff_zero]
    rwa [coeff_map, IsLocalRing.residue_eq_zero_iff, hϖ, Ideal.mem_span_singleton] at hi
  refine h


@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ϖ : R}
  {F : Type u} [Field F] [Algebra R F]
  {j : F} [Fact (j ≠ 0)]
  {V : ValuationSubring F}
-- given
  (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
  (hVA : ∀ a : R, algebraMap R F a ∈ V)
  (hVm : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits)
  (hVj : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 → Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) :
-- imply
  ∃ 𝔓 : Ideal ↥(chartAlgFin R F j), 𝔓.IsPrime ∧
      (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔓 ↔ (b : F) ∈ V.nonunits) ∧
      algebraMap R ↥(chartAlgFin R F j) ϖ ∈ 𝔓 ∧
      𝔓 ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes := by
  classical
    have hXne : (X : R[X]).map (IsLocalRing.residue R) ≠ 0 := by
-- proof
      rw [Polynomial.map_X]
      exact X_ne_zero
    have hjV : j ∈ V := by
      have h := (hVj X hXne).1
      rwa [aeval_X] at h
    let V' : Subalgebra R F := { V.toSubring.toSubsemiring with algebraMap_mem' := hVA }
    have hadjV : Algebra.adjoin R ({j} : Set F) ≤ V' := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjV)
    have hadjV' : ∀ x : ↥(Algebra.adjoin R ({j} : Set F)), (x : F) ∈ V := fun x => hadjV x.2
    let φ : ↥(Algebra.adjoin R ({j} : Set F)) →+* ↥V :=
      ((Algebra.adjoin R ({j} : Set F)).val : ↥(Algebra.adjoin R ({j} : Set F)) →+* F).codRestrict V hadjV'
    have hCV : ∀ b : ↥(chartAlgFin R F j), (b : F) ∈ V := by
      intro b
      have hb : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) (b : F) := b.2
      have hbV : IsIntegral ↥V (b : F) :=
        hb.map_of_comp_eq φ (RingHom.id F) (by ext; rfl)
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := F)).mp hbV
      rw [← hy]
      apply y.2
    let ψ : ↥(chartAlgFin R F j) →+* ↥V :=
      ((chartAlgFin R F j).val : ↥(chartAlgFin R F j) →+* F).codRestrict V hCV
    let 𝔓 : Ideal ↥(chartAlgFin R F j) := (IsLocalRing.maximalIdeal ↥V).comap ψ
    have h𝔓mem : ∀ b : ↥(chartAlgFin R F j), b ∈ 𝔓 ↔ (b : F) ∈ V.nonunits := fun b => by
      rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
      apply Iff.rfl
    have h𝔓prime : 𝔓.IsPrime := Ideal.comap_isPrime ψ _
    have hϖmax : ϖ ∈ IsLocalRing.maximalIdeal R := by
      rw [hϖ]
      exact Ideal.mem_span_singleton_self ϖ
    have hϖ𝔓 : algebraMap R ↥(chartAlgFin R F j) ϖ ∈ 𝔓 := by
      rw [h𝔓mem, Subalgebra.coe_algebraMap]
      exact hVm ϖ hϖmax
    refine ⟨𝔓, h𝔓prime, h𝔓mem, hϖ𝔓, ⟨h𝔓prime, (Ideal.span_singleton_le_iff_mem _).mpr hϖ𝔓⟩, ?_⟩
    rintro Q ⟨hQprime, hϖQ⟩ hQP
    rw [Ideal.span_singleton_le_iff_mem] at hϖQ
    let algS : Algebra ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) :=
      (Subalgebra.inclusion (adjoin_le_chartAlg R F ({j} : Set F))).toRingHom.toAlgebra
    have : IsScalarTower ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) F :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    by_contra hne
    obtain ⟨x, hx𝔓, hxQ⟩ := SetLike.not_le_iff_exists.mp hne
    have hxint : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) x := by
      have hx : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) (x : F) := x.2
      exact (isIntegral_algHom_iff
        (IsScalarTower.toAlgHom ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) F)
        (fun a b h => Subtype.ext h)).mp hx
    have : Q.IsPrime := hQprime
    have hlt := Ideal.under_lt_under_of_integral_mem_sdiff hQP ⟨hx𝔓, hxQ⟩ hxint
    refine hlt.2 (fun s hs => ?_)
    replace hs : algebraMap ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) s ∈ 𝔓 := hs
    show algebraMap ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) s ∈ Q
    obtain ⟨P, hP⟩ : ∃ P : R[X], aeval j P = (s : F) := by
      have h : (s : F) ∈ (aeval j : R[X] →ₐ[R] F).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]
        apply s.2
      refine h
    by_cases hPr : P.map (IsLocalRing.residue R) = 0
    ·
      obtain ⟨P₁, rfl⟩ := exists_eq_C_mul_of_map_residue_eq_zero ϖ hϖ P hPr
      have hmem₁ : aeval j P₁ ∈ chartAlgFin R F j :=
        adjoin_le_chartAlg R F ({j} : Set F)
          (by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨P₁, rfl⟩)
      have heq : algebraMap ↥(Algebra.adjoin R ({j} : Set F)) ↥(chartAlgFin R F j) s =
          algebraMap R ↥(chartAlgFin R F j) ϖ * ⟨aeval j P₁, hmem₁⟩ := by
        apply Subtype.ext
        rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
        show (s : F) = algebraMap R F ϖ * aeval j P₁
        rw [← hP, map_mul, Polynomial.aeval_C]
      rw [heq]
      exact Q.mul_mem_right _ hϖQ
    ·
      have hsnu : (s : F) ∈ V.nonunits := (h𝔓mem _).mp hs
      obtain ⟨-, hinv⟩ := hVj P hPr
      rw [hP] at hinv
      rcases (ValuationSubring.mem_nonunits_iff_or (A := V)).mp hsnu with h0 | hni
      ·
        have hs0 : s = 0 := Subtype.ext h0
        rw [hs0, map_zero]
        apply Q.zero_mem
      · exact absurd hinv hni


-- created on 2026-10-23

