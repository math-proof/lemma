import Mathlib

set_option autoImplicit false

noncomputable section

namespace PadicAlgCl

variable (p : ℕ) [Fact p.Prime]

def ringOfIntegers (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Subalgebra ℤ_[p] (PadicAlgCl p) :=
  integralClosure ℤ_[p] (PadicAlgCl p) ⊓ K.toSubalgebra.restrictScalars ℤ_[p]

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem mem_ringOfIntegers_iff (x : PadicAlgCl p) :
    x ∈ ringOfIntegers p K ↔ IsIntegral ℤ_[p] x ∧ x ∈ K := Iff.rfl

theorem ringOfIntegers_le_integralClosure :
    ringOfIntegers p K ≤ integralClosure ℤ_[p] (PadicAlgCl p) := inf_le_left

namespace ringOfIntegers

variable {p K}

theorem coe_mem (x : ringOfIntegers p K) : (x : PadicAlgCl p) ∈ K := x.2.2

theorem isIntegral_coe (x : ringOfIntegers p K) : IsIntegral ℤ_[p] (x : PadicAlgCl p) := x.2.1

variable (p K)

theorem algebraMap_mem (a : ℤ_[p]) : algebraMap ℤ_[p] (PadicAlgCl p) a ∈ ringOfIntegers p K :=
  Subalgebra.algebraMap_mem _ a

theorem natCast_mem (n : ℕ) : (n : PadicAlgCl p) ∈ ringOfIntegers p K := by
  rw [← map_natCast (algebraMap ℤ_[p] (PadicAlgCl p)) n]
  exact algebraMap_mem p K n

theorem algebraMap_coe (x : ringOfIntegers p K) :
    algebraMap (ringOfIntegers p K) (PadicAlgCl p) x = (x : PadicAlgCl p) := rfl

theorem algebraMap_injective_padicInt :
    Function.Injective (algebraMap ℤ_[p] (PadicAlgCl p)) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p)]
  exact (algebraMap ℚ_[p] (PadicAlgCl p)).injective.comp
    (IsFractionRing.injective ℤ_[p] ℚ_[p])

theorem norm_algebraMap_padicInt (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (PadicAlgCl p) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
  exact (norm_algebraMap' (PadicAlgCl p) (a : ℚ_[p])).trans (PadicInt.padic_norm_e_of_padicInt a)

theorem norm_le_one_of_isIntegral {x : PadicAlgCl p} (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  obtain ⟨f, hf, hfx⟩ := hx
  by_contra hlt
  push Not at hlt
  set n := f.natDegree with hn
  have heval : x ^ n = -∑ i ∈ Finset.range n, algebraMap ℤ_[p] (PadicAlgCl p) (f.coeff i) * x ^ i := by
    have h1 : Polynomial.eval₂ (algebraMap ℤ_[p] (PadicAlgCl p)) x f = 0 := hfx
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at h1
    have hlead : f.coeff n = 1 := hf
    rw [hlead, map_one, one_mul] at h1
    exact eq_neg_of_add_eq_zero_right h1
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  ·
    rw [hn0, Finset.range_zero, Finset.sum_empty, neg_zero, pow_zero] at heval
    exact one_ne_zero heval
  have hne : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.2 hnpos⟩
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
    (fun i => algebraMap ℤ_[p] (PadicAlgCl p) (f.coeff i) * x ^ i)
  rw [Finset.mem_range] at hi
  have hterm : ‖algebraMap ℤ_[p] (PadicAlgCl p) (f.coeff i) * x ^ i‖ < ‖x‖ ^ n := by
    rw [norm_mul, norm_pow, norm_algebraMap_padicInt]
    calc ‖f.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
          gcongr; exact PadicInt.norm_le_one _
      _ = ‖x‖ ^ i := one_mul _
      _ < ‖x‖ ^ n := pow_lt_pow_right₀ hlt hi
  have hxn : ‖x‖ ^ n = ‖∑ i ∈ Finset.range n, algebraMap ℤ_[p] (PadicAlgCl p) (f.coeff i) * x ^ i‖ := by
    rw [← norm_pow, heval, norm_neg]
  rw [hxn] at hterm
  exact absurd (hle.trans_lt hterm) (lt_irrefl _)

theorem norm_coe_le_one (x : ringOfIntegers p K) : ‖(x : PadicAlgCl p)‖ ≤ 1 :=
  norm_le_one_of_isIntegral p (isIntegral_coe x)

theorem not_isUnit_natCast : ¬ IsUnit ((p : ℕ) : ringOfIntegers p K) := by
  rintro ⟨u, hu⟩
  have hp : ((u : ringOfIntegers p K) : PadicAlgCl p) = (p : PadicAlgCl p) := by
    rw [hu]; rfl
  have hinv' : (((u⁻¹ : (ringOfIntegers p K)ˣ) : ringOfIntegers p K) : PadicAlgCl p) *
      (p : PadicAlgCl p) = 1 := by
    rw [← hp, ← Subalgebra.coe_mul, Units.inv_mul, Subalgebra.coe_one]
  have hnorm : ‖(((u⁻¹ : (ringOfIntegers p K)ˣ) : ringOfIntegers p K) : PadicAlgCl p)‖ *
      ‖(p : PadicAlgCl p)‖ = 1 := by
    rw [← norm_mul, hinv', norm_one]
  have hpnorm : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hle := norm_coe_le_one p K ((u⁻¹ : (ringOfIntegers p K)ˣ) : ringOfIntegers p K)
  have hlt : ‖(((u⁻¹ : (ringOfIntegers p K)ˣ) : ringOfIntegers p K) : PadicAlgCl p)‖ *
      ‖(p : PadicAlgCl p)‖ < 1 :=
    calc _ ≤ 1 * ‖(p : PadicAlgCl p)‖ := by gcongr
      _ < 1 := by rw [one_mul]; exact hpnorm
  rw [hnorm] at hlt
  exact lt_irrefl _ hlt

theorem span_natCast_ne_top : Ideal.span {((p : ℕ) : ringOfIntegers p K)} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  exact not_isUnit_natCast p K

theorem apply_coe_eq_of_mem_fixingSubgroup {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hσ : σ ∈ K.fixingSubgroup) (x : ringOfIntegers p K) : σ (x : PadicAlgCl p) = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (coe_mem x)

def algEquivOfMemFixingSubgroup (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ringOfIntegers p K] PadicAlgCl p :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => apply_coe_eq_of_mem_fixingSubgroup p K hσ x

theorem algEquivOfMemFixingSubgroup_apply (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ K.fixingSubgroup) (x : PadicAlgCl p) :
    algEquivOfMemFixingSubgroup p K σ hσ x = σ x := rfl

def galToAlgEquiv : K.fixingSubgroup →* (PadicAlgCl p ≃ₐ[ringOfIntegers p K] PadicAlgCl p) where
  toFun σ := algEquivOfMemFixingSubgroup p K σ σ.2
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

theorem galToAlgEquiv_apply (σ : K.fixingSubgroup) (x : PadicAlgCl p) :
    galToAlgEquiv p K σ x = (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x := rfl

theorem exists_pow_natCast_mul_mem {x : PadicAlgCl p} (hx : x ∈ K) :
    ∃ (m : ℕ) (y : ringOfIntegers p K), (y : PadicAlgCl p) = (p : PadicAlgCl p) ^ m * x := by
  have halg : IsAlgebraic ℤ_[p] x :=
    (IsFractionRing.isAlgebraic_iff ℤ_[p] ℚ_[p] (PadicAlgCl p)).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hint⟩ := IsAlgebraic.exists_integral_multiple halg

  set m := (d : ℤ_[p]).valuation with hm
  have hu := PadicInt.unitCoeff_spec hd0
  set u := PadicInt.unitCoeff hd0
  refine ⟨m, ⟨(algebraMap ℤ_[p] (PadicAlgCl p) ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) * (d • x), ?_⟩, ?_⟩
  · refine Subalgebra.mul_mem _ (algebraMap_mem p K _) ⟨hint, ?_⟩
    show d • x ∈ K.toSubalgebra.restrictScalars ℤ_[p]
    rw [Subalgebra.mem_restrictScalars, IntermediateField.mem_toSubalgebra, Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    exact K.mul_mem (K.algebraMap_mem _) hx
  · show algebraMap ℤ_[p] (PadicAlgCl p) ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (d • x) = _
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul]
    conv_lhs => rw [hu, ← mul_assoc, Units.inv_mul, one_mul, map_pow, map_natCast]

theorem apply_eq_self_of_mem (τ : PadicAlgCl p ≃ₐ[ringOfIntegers p K] PadicAlgCl p)
    {x : PadicAlgCl p} (hx : x ∈ K) : τ x = x := by
  obtain ⟨m, y, hy⟩ := exists_pow_natCast_mul_mem p K hx
  have hp0 : ((p : PadicAlgCl p) ^ m) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hτy : τ (y : PadicAlgCl p) = y := τ.commutes y
  rw [hy, map_mul, map_pow, map_natCast] at hτy
  exact mul_left_cancel₀ hp0 hτy

def restrictScalarsRat (τ : PadicAlgCl p ≃ₐ[ringOfIntegers p K] PadicAlgCl p) :
    PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p :=
  AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun a => apply_eq_self_of_mem p K τ (K.algebraMap_mem a)

theorem restrictScalarsRat_apply (τ : PadicAlgCl p ≃ₐ[ringOfIntegers p K] PadicAlgCl p)
    (x : PadicAlgCl p) : restrictScalarsRat p K τ x = τ x := rfl

theorem restrictScalarsRat_mem_fixingSubgroup (τ : PadicAlgCl p ≃ₐ[ringOfIntegers p K] PadicAlgCl p) :
    restrictScalarsRat p K τ ∈ K.fixingSubgroup :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun _ hx => apply_eq_self_of_mem p K τ hx

theorem algEquivOfMemFixingSubgroup_restrictScalarsRat
    (τ : PadicAlgCl p ≃ₐ[ringOfIntegers p K] PadicAlgCl p) :
    algEquivOfMemFixingSubgroup p K (restrictScalarsRat p K τ)
      (restrictScalarsRat_mem_fixingSubgroup p K τ) = τ := AlgEquiv.ext fun _ => rfl

theorem restrictScalarsRat_algEquivOfMemFixingSubgroup (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ K.fixingSubgroup) :
    restrictScalarsRat p K (algEquivOfMemFixingSubgroup p K σ hσ) = σ := AlgEquiv.ext fun _ => rfl

end ringOfIntegers

end PadicAlgCl

end
