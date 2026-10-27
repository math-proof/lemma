import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsDiscreteValuationRing_exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional.lean)
-/
@[path]
private lemma main
  {L : Type} [Field L]
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (F : Type) [Field F] [Algebra O F] [IsFractionRing O F]
  (A : ValuationSubring L)
  (K' : Subfield L) [Algebra O K'] [Algebra F K'] [IsScalarTower O F K'] [FiniteDimensional F K'] [Algebra.IsSeparable F K']
  (ιA : O →+* A) [IsLocalHom ιA]
  -- given
  (hιA : ∀ x : O, ((ιA x : A) : L) = ((algebraMap O K' x : K') : L)) :
  -- imply
  ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (σ : O →+* O') (ι' : O' →+* A) (j' : O' →+* K'), Function.Injective ι' ∧ IsLocalHom ι' ∧ ι'.comp σ = ιA ∧ (∀ x : O', ((ι' x : A) : L) = ((j' x : K') : L)) ∧ j'.comp σ = algebraMap O K' ∧ (∀ c : K', ∃ a b : O', j' b ≠ 0 ∧ c * j' b = j' a) := by
  -- proof
  classical
  let _ : IsDedekindDomain (integralClosure O K') := integralClosure.isDedekindDomain O F K'
  let _ : IsFractionRing (integralClosure O K') K' := integralClosure.isFractionRing_of_finite_extension F K'
  set D := integralClosure O K' with hD
  have hinjOK : Function.Injective (algebraMap O K') := by
    rw [IsScalarTower.algebraMap_eq O F K']
    apply (algebraMap F K').injective.comp (IsFractionRing.injective O F)
  have hinjO : Function.Injective ιA := by
    intro a b h
    have := congrArg (fun z : A => (z : L)) h
    simp only [hιA] at this
    apply hinjOK (Subtype.ext this)
  have hv : A.valuation.Integers A :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun a => A.valuation_le_one a
      exists_of_le_one := fun r hr => ⟨⟨r, A.mem_of_valuation_le_one r hr⟩, rfl⟩ }
  have hcomp : (algebraMap A L).comp ιA = K'.subtype.comp (algebraMap O K') := by
    ext x
    apply hιA x
  have hDA : ∀ d : D, ((d : K') : L) ∈ A := by
    intro d
    apply A.mem_of_valuation_le_one _ ((Valuation.mem_integer_iff _ _).mp (hv.mem_of_integral (IsIntegral.map_of_comp_eq ιA K'.subtype hcomp d.2)))
  let φ : D →+* A :=
    { toFun := fun d => ⟨((d : K') : L), hDA d⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intros
        ext
        simp
      map_zero' := by
        ext
        simp
      map_add' := by
        intros
        ext
        simp }
  have hφ : ∀ d : D, ((φ d : A) : L) = ((d : K') : L) := fun d => rfl
  have hφO : φ.comp (algebraMap O D) = ιA := by
    ext x
    show (((algebraMap O D x : D) : K') : L) = ((ιA x : A) : L)
    rw [hιA]
    rfl
  let 𝔭 : Ideal D := (maximalIdeal A).comap φ
  let h𝔭p : 𝔭.IsPrime := Ideal.IsPrime.comap φ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hφOx : ∀ x : O, φ (algebraMap O D x) = ιA x := fun x => congrArg (fun f : O →+* A => f x) hφO
  have h𝔭0 : 𝔭 ≠ ⊥ := by
    intro h
    have hmem : algebraMap O D ϖ ∈ 𝔭 := by
      show φ (algebraMap O D ϖ) ∈ maximalIdeal A
      rw [hφOx]
      apply (map_mem_nonunits_iff ιA ϖ).mpr hϖ.not_isUnit
    rw [h, Ideal.mem_bot] at hmem
    apply hϖ.ne_zero
    apply hinjOK
    rw [map_zero]
    have := congrArg (fun d : D => (d : K')) hmem
    simpa using this
  let _ : IsDiscreteValuationRing (Localization.AtPrime 𝔭) := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain D h𝔭0 _
  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (φ y) := by
    intro y
    by_contra hy
    apply y.2 ((mem_maximalIdeal _).mpr hy)
  let ι' : Localization.AtPrime 𝔭 →+* A := IsLocalization.lift (M := 𝔭.primeCompl) hunit
  have hunitK : ∀ y : 𝔭.primeCompl, IsUnit (algebraMap D K' y) := by
    intro y
    apply IsUnit.mk0
    intro h0
    apply y.2
    have : (y : D) = 0 := (FaithfulSMul.algebraMap_injective D K') (by rw [h0, map_zero])
    rw [this]
    apply Ideal.zero_mem _
  let j' : Localization.AtPrime 𝔭 →+* K' := IsLocalization.lift (M := 𝔭.primeCompl) hunitK
  let σ : O →+* Localization.AtPrime 𝔭 := (algebraMap D (Localization.AtPrime 𝔭)).comp (algebraMap O D)
  have hι'D : ∀ d : D, ι' (algebraMap D _ d) = φ d := fun d => IsLocalization.lift_eq hunit d
  have hj'D : ∀ d : D, j' (algebraMap D _ d) = (d : K') := fun d => IsLocalization.lift_eq hunitK d
  have hagree : (algebraMap A L).comp ι' = K'.subtype.comp j' := by
    apply IsLocalization.ringHom_ext (M := 𝔭.primeCompl)
    ext d
    simp only [RingHom.comp_apply, hι'D, hj'D]
    rfl
  refine ⟨Localization.AtPrime 𝔭, inferInstance, inferInstance, inferInstance, σ, ι', j', ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hφinj : Function.Injective φ := by
      intro a b h
      have : ((a : K') : L) = ((b : K') : L) := by rw [← hφ a, ← hφ b, h]
      apply Subtype.ext (Subtype.ext this)
    have halg : Function.Injective (algebraMap D (Localization.AtPrime 𝔭)) := IsLocalization.injective (Localization.AtPrime 𝔭) 𝔭.primeCompl_le_nonZeroDivisors
    refine (IsLocalization.lift_injective_iff hunit).mpr fun x y => ?_
    constructor
    ·
      intro h
      rw [halg h]
    ·
      intro h
      rw [hφinj h]
  ·
    constructor
    intro x hx
    obtain ⟨⟨d, s⟩, hds⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl x
    dsimp only at hds
    rw [← hds] at hx ⊢
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro hd
    have : IsUnit (φ d) := by
      have e : ι' (IsLocalization.mk' _ d s) * φ s = φ d := by
        rw [← hι'D s, ← map_mul, IsLocalization.mk'_spec, hι'D]
      rw [← e]
      apply hx.mul (hunit s)
    apply ((mem_maximalIdeal _).mp hd) this
  ·
    refine RingHom.ext fun x => ?_
    show ι' (algebraMap D _ (algebraMap O D x)) = ιA x
    rw [hι'D, hφOx]
  ·
    intro x
    apply congrArg (fun f : Localization.AtPrime 𝔭 →+* L => f x) hagree
  ·
    refine RingHom.ext fun x => ?_
    show j' (algebraMap D _ (algebraMap O D x)) = algebraMap O K' x
    rw [hj'D]
    rfl
  ·
    intro c
    obtain ⟨⟨d, e⟩, hde⟩ := IsLocalization.mk'_surjective (nonZeroDivisors D) c
    dsimp only at hde
    refine ⟨algebraMap D _ d, algebraMap D _ (e : D), ?_, ?_⟩
    ·
      rw [hj'D]
      apply IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors K' le_rfl e.2
    ·
      rw [hj'D, hj'D, ← hde]
      apply IsLocalization.mk'_spec K' d e


-- created on 2026-10-20
