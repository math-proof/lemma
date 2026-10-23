import Lemma.Definitions.Def_AlgebraicCurve_FrobeniusEndo

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section PlaceCalculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem _root_.ValuationSubring.pow_mem_iff (A : ValuationSubring F) {n : ℕ} (hn : n ≠ 0)
    (x : F) :
    x ^ n ∈ A ↔ x ∈ A := by
  refine ⟨fun hxn => ?_, fun hx => pow_mem hx n⟩
  rcases A.mem_or_inv_mem x with hx | hxi
  · exact hx
  · rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_mem A
    · have hkey : x = x ^ n * (x⁻¹) ^ (n - 1) := by
        rw [inv_pow, eq_comm, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hx0), ← pow_succ']
        congr 1
        omega
      rw [hkey]
      exact mul_mem hxn (pow_mem hxi _)

private theorem Place.ord_pow (v : Place K F) (f : F) (n : ℕ) :
    v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  rwa [zpow_natCast] at this

variable {φ : F →ₐ[K] F} {ℓ : ℕ}

theorem IsFrobeniusEndo.restrictAlong_injective (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0)
    (hφ : φ.toRingHom.IsIntegral) :
    Function.Injective (Place.restrictAlong φ hφ) := by
  intro w₁ w₂ hw
  have hval : ∀ w : Place K F, (w.restrictAlong φ hφ).toValuationSubring =
      w.toValuationSubring.comap φ.toRingHom := by
    intro w
    rfl
  refine Place.ext (SetLike.ext fun x => ?_)
  obtain ⟨y, hy⟩ := h.pow_mem_range x
  have key : ∀ w : Place K F,
      x ∈ w.toValuationSubring ↔ y ∈ (w.restrictAlong φ hφ).toValuationSubring := by
    intro w
    rw [hval, ValuationSubring.mem_comap]
    show x ∈ w.toValuationSubring ↔ φ y ∈ w.toValuationSubring
    rw [hy]
    exact (w.toValuationSubring.pow_mem_iff hℓ x).symm
  rw [key w₁, key w₂, hw]

theorem IsFrobeniusEndo.ramificationIndexAlong_eq (h : IsFrobeniusEndo ℓ φ)
    (hℓ : ℓ ≠ 0) (w : Place K F) :
    Place.ramificationIndexAlong φ w = ℓ := by
  letI := algebraAlong φ
  show w.ramificationIndex F = ℓ

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  obtain ⟨y, hy⟩ := h.pow_mem_range (π : F)
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact pow_ne_zero ℓ hπF hy.symm
  have hyord : w.ord (algebraMap F F y) = (ℓ : ℤ) := by
    show w.ord (φ y) = (ℓ : ℤ)
    rw [hy, w.ord_pow, w.ord_coe_irreducible hπ, mul_one]
  have hℓmem : ℓ ∈ {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F f) = n} :=
    ⟨Nat.pos_of_ne_zero hℓ, y, hy0, hyord⟩

  have hlb : ∀ n ∈ {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F f) = n}, ℓ ≤ n := by
    rintro n ⟨hn, f, hf, hford⟩
    obtain ⟨x, hx⟩ := h.mem_range_pow f
    have hford' : (n : ℤ) = ℓ * w.ord x := by
      rw [← hford]
      show w.ord (φ f) = ℓ * w.ord x
      rw [hx, w.ord_pow]
    have hxpos : 1 ≤ w.ord x := by
      by_cases hx1 : 1 ≤ w.ord x
      · exact hx1
      · exfalso
        have hle : (ℓ : ℤ) * w.ord x ≤ 0 :=
          mul_nonpos_iff.mpr (Or.inl ⟨by positivity, by omega⟩)
        omega
    have : (ℓ : ℤ) ≤ (n : ℤ) := by
      rw [hford']
      exact le_mul_of_one_le_right (by positivity) hxpos
    exact_mod_cast this
  exact le_antisymm (Nat.sInf_le hℓmem)
    (hlb _ (Nat.sInf_mem (Set.nonempty_of_mem hℓmem)))

theorem IsFrobeniusEndo.ord_restrictAlong_frobNorm (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0)
    (hφ : φ.toRingHom.IsIntegral) (w : Place K F) (f : F) :
    (w.restrictAlong φ hφ).ord (h.frobNorm f) = w.ord f := by
  have hkey : (ℓ : ℤ) * (w.restrictAlong φ hφ).ord (h.frobNorm f) = ℓ * w.ord f := by
    calc (ℓ : ℤ) * (w.restrictAlong φ hφ).ord (h.frobNorm f)
        = (Place.ramificationIndexAlong φ w : ℤ) *
            (w.restrictAlong φ hφ).ord (h.frobNorm f) := by
          rw [h.ramificationIndexAlong_eq hℓ]
      _ = w.ord (φ (h.frobNorm f)) := (w.ord_restrictAlong φ hφ (h.frobNorm f)).symm
      _ = w.ord (f ^ ℓ) := by rw [h.map_frobNorm]
      _ = ℓ * w.ord f := w.ord_pow f ℓ
  have hℓ0 : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hℓ
  exact mul_left_cancel₀ hℓ0 hkey

end PlaceCalculus

section NormFormula

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ]
variable {φ : F →ₐ[K] F}

theorem IsFrobeniusEndo.norm_eq_frobNorm (h : IsFrobeniusEndo ℓ φ)
    (hrank : finrankAlong K φ = ℓ) (f : F) :
    (letI := algebraAlong φ; Algebra.norm F f) = h.frobNorm f := by
  letI := algebraAlong φ
  have hpow : (Algebra.norm F f) ^ ℓ = (h.frobNorm f) ^ ℓ := by
    have h3 : Algebra.norm F (algebraMap F F (h.frobNorm f))
        = h.frobNorm f ^ finrankAlong K φ :=
      Algebra.norm_algebraMap (h.frobNorm f)
    calc (Algebra.norm F f) ^ ℓ
        = Algebra.norm F (f ^ ℓ) := (map_pow (Algebra.norm F) f ℓ).symm
      _ = Algebra.norm F (algebraMap F F (h.frobNorm f)) := by
          rw [show algebraMap F F (h.frobNorm f) = φ (h.frobNorm f) from rfl,
            h.map_frobNorm f]
      _ = h.frobNorm f ^ finrankAlong K φ := h3
      _ = h.frobNorm f ^ ℓ := by rw [hrank]
  exact frobenius_inj F ℓ hpow

theorem IsFrobeniusEndo.normFormulaAlong (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1) :
    NormFormulaAlong K φ hfin := by
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  intro f hf D hD v
  classical

  obtain ⟨w₀, hw₀⟩ := hsurj v

  rw [Divisor.pushforward_apply]
  have hw₀' : Place.restrict F w₀ = v := hw₀
  have hf1' : (Place.inertiaDeg F w₀ : ℤ) = 1 := by
    have := hf1 w₀
    exact_mod_cast (show Place.inertiaDeg F w₀ = 1 from this)
  have hcollapse : (∑ w ∈ D.support,
      if Place.restrict F w = v then D w * (Place.inertiaDeg F w : ℤ) else 0)
        = D w₀ * (Place.inertiaDeg F w₀ : ℤ) := by
    refine (Finset.sum_eq_single w₀ ?_ ?_).trans (if_pos hw₀')
    · intro w _ hwne
      rw [if_neg]
      intro hwv
      exact hwne (h.restrictAlong_injective hℓ hφ
        ((show Place.restrictAlong φ hφ w = v from hwv).trans hw₀.symm))
    · intro hw₀mem
      rw [Finsupp.notMem_support_iff.mp hw₀mem, zero_mul, ite_self]
  rw [hcollapse, hD w₀, hf1', mul_one]

  rw [h.norm_eq_frobNorm hrank f]
  rw [show v = w₀.restrictAlong φ hφ from hw₀.symm]
  exact (h.ord_restrictAlong_frobNorm hℓ hφ w₀ f).symm

end NormFormula

section Descent

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ]
variable (φ : F →ₐ[K] F)

def frobeniusPushforwardDegZero (hφ : φ.toRingHom.IsIntegral) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.pushforwardAlong φ hφ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.pushforwardAlong_mem_degZero φ hφ D.2)

@[simp]
theorem coe_frobeniusPushforwardDegZero (hφ : φ.toRingHom.IsIntegral)
    (D : Divisor.degZero (K := K) (F := F)) :
    (frobeniusPushforwardDegZero φ hφ D : Divisor K F)
      = Divisor.pushforwardAlong φ hφ (D : Divisor K F) :=
  rfl

def IsFrobeniusEndo.pushforwardPic0 (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1) :
    Pic0 K F →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (frobeniusPushforwardDegZero φ hφ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pushforwardAlong φ hφ hfin
      (h.normFormulaAlong hφ hfin hrank hsurj hf1) hD)

theorem IsFrobeniusEndo.pushforwardPic0_mk (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1)
    (D : Divisor.degZero (K := K) (F := F)) :
    (h.pushforwardPic0 φ hφ hfin hrank hsurj hf1) (Pic0.mk D)
      = Pic0.mk (frobeniusPushforwardDegZero φ hφ D) := by
  rfl

theorem IsFrobeniusEndo.isPrincipal_pushforwardAlong (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1)
    {D : Divisor K F} (hD : D.IsPrincipal) :
    (Divisor.pushforwardAlong φ hφ D).IsPrincipal :=
  Divisor.isPrincipal_pushforwardAlong φ hφ hfin
    (h.normFormulaAlong hφ hfin hrank hsurj hf1) hD

end Descent

section LocalConstant

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
variable {φ : F →ₐ[K] F} {ℓ : ℕ}

theorem IsFrobeniusEndo.fiberAlong_eq_singleton (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0)
    (hφ : φ.toRingHom.IsIntegral)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ)) (v : Place K F) :
    ∃ w₀ : Place K F, Place.fiberAlong φ hφ v = {w₀} := by
  obtain ⟨w₀, hw₀⟩ := hsurj v
  refine ⟨w₀, ?_⟩
  ext w
  simp only [Place.mem_fiberAlong, Finset.mem_singleton]
  constructor
  · intro hw
    exact h.restrictAlong_injective hℓ hφ (hw.trans hw₀.symm)
  · rintro rfl
    exact hw₀

theorem IsFrobeniusEndo.sum_fiberAlong_eq (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0)
    (hφ : φ.toRingHom.IsIntegral)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1) (v : Place K F) :
    ∑ w ∈ Place.fiberAlong φ hφ v,
        (Place.ramificationIndexAlong φ w : ℤ) * (Place.inertiaDegAlong φ hφ w : ℤ)
      = (ℓ : ℤ) := by
  obtain ⟨w₀, hfib⟩ := h.fiberAlong_eq_singleton hℓ hφ hsurj v
  rw [hfib, Finset.sum_singleton, h.ramificationIndexAlong_eq hℓ w₀, hf1 w₀]
  simp

theorem IsFrobeniusEndo.fundamentalIdentityAlong (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0)
    (hφ : φ.toRingHom.IsIntegral) (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1) :
    FundamentalIdentityAlong K φ hφ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : SumRamificationInertia K F F := by
    refine ⟨fun v => ?_⟩
    have hloc : ∑ w ∈ Place.fiberAlong φ hφ v,
        (Place.ramificationIndexAlong φ w : ℤ) * (Place.inertiaDegAlong φ hφ w : ℤ)
          = ((finrankAlong K φ : ℕ) : ℤ) := by
      rw [hrank]
      exact h.sum_fiberAlong_eq hℓ hφ hsurj hf1 v
    exact hloc
  exact instFundamentalIdentityOfSumRamificationInertia

end LocalConstant

section PullbackDescent

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
variable {ℓ : ℕ} [Fact ℓ.Prime] {φ : F →ₐ[K] F}

def IsFrobeniusEndo.frobeniusPullbackDegZero (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.pullbackAlong φ hφ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.pullbackAlong_mem_degZero φ hφ
      (h.fundamentalIdentityAlong (Fact.out : ℓ.Prime).ne_zero hφ hrank hsurj hf1) D.2)

@[simp]
theorem IsFrobeniusEndo.coe_frobeniusPullbackDegZero (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1)
    (D : Divisor.degZero (K := K) (F := F)) :
    (h.frobeniusPullbackDegZero hφ hrank hsurj hf1 D : Divisor K F)
      = Divisor.pullbackAlong φ hφ (D : Divisor K F) :=
  rfl

def IsFrobeniusEndo.pullbackPic0 (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1) :
    Pic0 K F →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (h.frobeniusPullbackDegZero hφ hrank hsurj hf1) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pullbackAlong φ hφ hD)

theorem IsFrobeniusEndo.pullbackPic0_mk (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1)
    (D : Divisor.degZero (K := K) (F := F)) :
    h.pullbackPic0 hφ hrank hsurj hf1 (Pic0.mk D)
      = Pic0.mk (h.frobeniusPullbackDegZero hφ hrank hsurj hf1 D) := by
  rfl

end PullbackDescent

end AlgebraicCurve
