module

public import Mathlib
public import Theorem.CuspForm.HeckeAlgebra
public import Def.HeckeGalois_EichlerShimura

public noncomputable section

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups

namespace ModularCurve

section Period


public theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _


public theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := max_le zero_le_one (min_le_right _ _)


public theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)


public theorem clamp01_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clamp01 t = t := by
  rw [clamp01, min_eq_left ht.2, max_eq_right ht.1]


public theorem segmentPoint_im_pos (τ₀ τ₁ : ℍ) (t : ℝ) : 0 < (segmentPoint τ₀ τ₁ t).im := by
  have h0 := clamp01_nonneg t
  have h1 := clamp01_le_one t
  simp only [segmentPoint, Complex.add_im, Complex.smul_im, smul_eq_mul]
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h]; simpa using τ₁.im_pos
  · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) τ₀.im_pos)
      (mul_nonneg h0 τ₁.im_pos.le)


public theorem continuous_segmentPoint (τ₀ τ₁ : ℍ) : Continuous (segmentPoint τ₀ τ₁) :=
  ((continuous_const.sub continuous_clamp01).smul continuous_const).add
    (continuous_clamp01.smul continuous_const)


@[simp] public theorem coe_segmentPath (τ₀ τ₁ : ℍ) (t : ℝ) :
    ((segmentPath τ₀ τ₁ t : ℍ) : ℂ) = segmentPoint τ₀ τ₁ t := rfl


public theorem continuous_segmentPath (τ₀ τ₁ : ℍ) : Continuous (segmentPath τ₀ τ₁) :=
  (continuous_segmentPoint τ₀ τ₁).upperHalfPlaneMk _

variable (N : ℕ)


public theorem continuous_periodIntegrand (τ₀ τ₁ : ℍ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    Continuous (periodIntegrand N τ₀ τ₁ f) :=
  ((f.holo'.continuous).comp (continuous_segmentPath τ₀ τ₁)).mul continuous_const


public theorem intervalIntegrable_periodIntegrand (τ₀ τ₁ : ℍ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (a b : ℝ) :
    IntervalIntegrable (periodIntegrand N τ₀ τ₁ f) MeasureTheory.volume a b :=
  (continuous_periodIntegrand N τ₀ τ₁ f).intervalIntegrable a b


public theorem periodIntegrand_add (τ₀ τ₁ : ℍ) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    periodIntegrand N τ₀ τ₁ (f + g) = periodIntegrand N τ₀ τ₁ f + periodIntegrand N τ₀ τ₁ g := by
  funext t
  simp [periodIntegrand, add_mul]


public theorem periodIntegrand_smul (τ₀ τ₁ : ℍ) (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    periodIntegrand N τ₀ τ₁ (c • f) = fun t => c * periodIntegrand N τ₀ τ₁ f t := by
  funext t
  simp [periodIntegrand, mul_assoc]


public theorem periodAlong_apply (τ₀ τ₁ : ℍ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    periodAlong N τ₀ τ₁ f = ∫ t in (0 : ℝ)..1, f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀) :=
  rfl


public theorem period_apply (γ : CongruenceSubgroup.Gamma0 N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    period N γ f =
      ∫ t in (0 : ℝ)..1, f (segmentPath UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I) t) *
        ((((γ : SL(2, ℤ)) • UpperHalfPlane.I : ℍ) : ℂ) - (UpperHalfPlane.I : ℂ)) :=
  rfl


public theorem period_mem_periodLattice (γ : CongruenceSubgroup.Gamma0 N) : period N γ ∈ periodLattice N :=
  Submodule.subset_span (Set.mem_range_self γ)

end Period

section Hecke

variable (N : ℕ) [NeZero N]


public theorem cuspHeckeGen_of_dvd (ℓ : Nat.Primes) (h : (ℓ : ℕ) ∣ N) :
    (cuspHeckeGen N ℓ : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) =
      CuspForm.heckeULin 2 h := by
  rw [cuspHeckeGen, dif_pos h]; rfl


public theorem cuspHeckeGen_of_not_dvd (ℓ : Nat.Primes) (h : ¬ (ℓ : ℕ) ∣ N) :
    (cuspHeckeGen N ℓ : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) =
      CuspForm.heckeTLin 2 ℓ.prop h := by
  rw [cuspHeckeGen, dif_neg h]; rfl


@[simp] public theorem cuspHeckeAeval_heckeGen (ℓ : Nat.Primes) :
    cuspHeckeAeval N (heckeGen ℓ) = cuspHeckeGen N ℓ :=
  MvPolynomial.aeval_X _ ℓ


public theorem range_cuspHeckeGen : Set.range (cuspHeckeGen N) =
    {x : CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) |
      (x : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) ∈
        CuspForm.heckeGenerators N 2 (∅ : Set ℕ)} := by
  ext x
  constructor
  · rintro ⟨ℓ, rfl⟩
    by_cases h : (ℓ : ℕ) ∣ N
    · rw [Set.mem_setOf_eq, cuspHeckeGen_of_dvd N ℓ h]
      exact CuspForm.heckeULin_mem_heckeGenerators ℓ.prop h (Set.notMem_empty _)
    · rw [Set.mem_setOf_eq, cuspHeckeGen_of_not_dvd N ℓ h]
      exact CuspForm.heckeTLin_mem_heckeGenerators ℓ.prop h (Set.notMem_empty _)
  · rintro (⟨ℓ, hℓ, hℓN, -, hx⟩ | ⟨q, hqN, hq, -, hx⟩)
    · refine ⟨⟨ℓ, hℓ⟩, Subtype.ext ?_⟩
      rw [hx]; exact cuspHeckeGen_of_not_dvd N ⟨ℓ, hℓ⟩ hℓN
    · refine ⟨⟨q, hq⟩, Subtype.ext ?_⟩
      rw [hx]; exact cuspHeckeGen_of_dvd N ⟨q, hq⟩ hqN


public theorem cuspHeckeAeval_range : (cuspHeckeAeval N).range = ⊤ := by
  rw [cuspHeckeAeval, ← Algebra.adjoin_range_eq_range_aeval, range_cuspHeckeGen]
  set H := CuspForm.heckeAlgebra N 2 (∅ : Set ℕ)
  apply Subalgebra.map_injective (f := H.val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  have himg : (H.val : H → Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) ''
      {x : H | (x : Module.End ℂ _) ∈ CuspForm.heckeGenerators N 2 (∅ : Set ℕ)} =
      CuspForm.heckeGenerators N 2 (∅ : Set ℕ) := by
    ext T
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hT
      exact ⟨⟨T, Algebra.subset_adjoin hT⟩, hT, rfl⟩
  rw [himg]
  rfl


public theorem cuspHeckeRep_apply (t : HeckeAlg) :
    cuspHeckeRep N t = (cuspHeckeAeval N t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :=
  rfl


public theorem cuspHeckeRep_heckeGen (ℓ : Nat.Primes) :
    cuspHeckeRep N (heckeGen ℓ) = (cuspHeckeGen N ℓ : Module.End ℂ _) := by
  rw [cuspHeckeRep_apply, cuspHeckeAeval_heckeGen]


public theorem cuspHeckeRep_mem (t : HeckeAlg) : cuspHeckeRep N t ∈ CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) :=
  (cuspHeckeAeval N t).2


public theorem range_cuspHeckeRep :
    Set.range (cuspHeckeRep N) = (CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) : Set _) := by
  ext T
  constructor
  · rintro ⟨t, rfl⟩; exact cuspHeckeRep_mem N t
  · intro hT
    have : (⟨T, hT⟩ : CuspForm.heckeAlgebra N 2 (∅ : Set ℕ)) ∈ (cuspHeckeAeval N).range := by
      rw [cuspHeckeAeval_range]; trivial
    obtain ⟨t, ht⟩ := this
    exact ⟨t, congrArg Subtype.val ht⟩


public theorem cuspHeckeRep_comm (s t : HeckeAlg) :
    cuspHeckeRep N s * cuspHeckeRep N t = cuspHeckeRep N t * cuspHeckeRep N s := by
  rw [← map_mul, ← map_mul, mul_comm]


public theorem dualHeckeRep_apply (t : HeckeAlg) :
    dualHeckeRep N t = (cuspHeckeRep N t).dualMap := rfl


@[simp] public theorem dualHeckeRep_apply_apply (t : HeckeAlg)
    (φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    dualHeckeRep N t φ f = φ (cuspHeckeRep N t f) := rfl


public theorem dualHeckeRep_C (a : ℤ) (φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :
    dualHeckeRep N (MvPolynomial.C a) φ = a • φ := by
  ext f
  rw [dualHeckeRep_apply_apply, ← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast,
    Module.End.intCast_apply, map_zsmul, LinearMap.smul_apply]


public theorem periodLattice_stable_of (h : PeriodLatticeHeckeStable N) (t : HeckeAlg)
    (x : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) (hx : x ∈ periodLattice N) :
    dualHeckeRep N t x ∈ periodLattice N := by
  induction t using MvPolynomial.induction_on generalizing x with
  | C a => rw [dualHeckeRep_C]; exact Submodule.smul_mem _ a hx
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ (hp x hx) (hq x hx)
  | mul_X p ℓ hp =>
    rw [map_mul, Module.End.mul_apply]
    exact hp _ (h ℓ x hx)

variable (N)


@[simp] public theorem coe_periodLatticeRestrict_apply (h : PeriodLatticeHeckeStable N) (t : HeckeAlg)
    (x : periodLattice N) :
    ((periodLatticeRestrict N h t x : periodLattice N) : Module.Dual ℂ _) = dualHeckeRep N t x :=
  rfl


public theorem coe_periodLatticeHeckeEnd_apply (h : PeriodLatticeHeckeStable N) (t : HeckeAlg)
    (x : periodLattice N) :
    ((periodLatticeHeckeEnd N t x : periodLattice N) : Module.Dual ℂ _) = dualHeckeRep N t x := by
  have e : periodLatticeHeckeEnd N = periodLatticeRestrictHom N h := dif_pos h
  rw [e]; rfl


public theorem periodLatticeHeckeEnd_of_not (h : ¬ PeriodLatticeHeckeStable N) (t : HeckeAlg)
    (x : periodLattice N) :
    periodLatticeHeckeEnd N t x = MvPolynomial.constantCoeff t • x := by
  have e : periodLatticeHeckeEnd N = (Int.castRingHom (Module.End ℤ (periodLattice N))).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ)) := dif_neg h
  rw [e, RingHom.comp_apply, MvPolynomial.eval₂Hom_zero_apply]
  simp only [eq_intCast, Int.cast_id, Module.End.intCast_apply]

variable (N)


public theorem periodLatticeModule_smul_def (t : HeckeAlg) (x : periodLattice N) :
    (letI : Module HeckeAlg (periodLattice N) := periodLatticeModule N; t • x) =
      periodLatticeHeckeEnd N t x :=
  rfl

end Hecke

end ModularCurve

end
