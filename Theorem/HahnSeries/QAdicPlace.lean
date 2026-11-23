module

public import Theorem.HahnSeries.X0
public import Theorem.Valuation.DivisorClassGroup

public noncomputable section

set_option autoImplicit false

noncomputable section

open IntermediateField HahnSeries AlgebraicCurve Valuation

namespace ModularCurve

public theorem order_jq : jq.order = -1 := by
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [coeff_jq_neg_one]; exact one_ne_zero)) ?_
  by_contra! h
  exact HahnSeries.coeff_order_eq_zero.not.mpr jq_ne_zero (coeff_jq_of_lt h)

variable (L : Type*) [Field L]

section OrderArithBar

variable {L}


public theorem order_mul_of_ne_zero_bar {f g : LaurentSeries L} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).order = f.order + g.order :=
  HahnSeries.order_mul_of_ne_zero
    (mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hf)
      (HahnSeries.leadingCoeff_ne_zero.mpr hg))


public theorem order_inv_of_ne_zero_bar {f : LaurentSeries L} (hf : f ≠ 0) :
    (f⁻¹).order = -f.order := by
  have h := order_mul_of_ne_zero_bar hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, HahnSeries.order_one] at h
  omega


public theorem order_pow_of_ne_zero_bar {f : LaurentSeries L} (hf : f ≠ 0) (n : ℕ) :
    (f ^ n).order = n * f.order := by
  induction n with
  | zero => simp [HahnSeries.order_one]
  | succ k ih =>
      rw [pow_succ, order_mul_of_ne_zero_bar (pow_ne_zero k hf) hf, ih]
      push_cast
      ring


public theorem order_zpow_of_ne_zero_bar {f : LaurentSeries L} (hf : f ≠ 0) (n : ℤ) :
    (f ^ n).order = n * f.order := by
  rcases Int.natAbs_eq n with h | h
  · rw [h, zpow_natCast, order_pow_of_ne_zero_bar hf]
  · rw [h, zpow_neg, zpow_natCast,
      order_inv_of_ne_zero_bar (pow_ne_zero _ hf), order_pow_of_ne_zero_bar hf]
    ring


public theorem order_div_of_ne_zero_bar {f g : LaurentSeries L} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f / g).order = f.order - g.order := by
  rw [div_eq_mul_inv, order_mul_of_ne_zero_bar hf (inv_ne_zero hg),
    order_inv_of_ne_zero_bar hg]
  ring

end OrderArithBar

section QSeriesBar

variable (F : IntermediateField L (LaurentSeries L))


@[simp] public theorem qSeriesBar_zero : qSeriesBar L F 0 = 0 := rfl


@[simp] public theorem qSeriesBar_one : qSeriesBar L F 1 = 1 := rfl


@[simp] public theorem qSeriesBar_mul (f g : F) :
    qSeriesBar L F (f * g) = qSeriesBar L F f * qSeriesBar L F g := rfl


@[simp] public theorem qSeriesBar_add (f g : F) :
    qSeriesBar L F (f + g) = qSeriesBar L F f + qSeriesBar L F g := rfl


@[simp] public theorem qSeriesBar_neg (f : F) : qSeriesBar L F (-f) = -(qSeriesBar L F f) := rfl


@[simp] public theorem qSeriesBar_sub (f g : F) :
    qSeriesBar L F (f - g) = qSeriesBar L F f - qSeriesBar L F g := rfl


@[simp] public theorem qSeriesBar_inv (f : F) : qSeriesBar L F f⁻¹ = (qSeriesBar L F f)⁻¹ := rfl


@[simp] public theorem qSeriesBar_div (f g : F) :
    qSeriesBar L F (f / g) = qSeriesBar L F f / qSeriesBar L F g := rfl


@[simp] public theorem qSeriesBar_pow (f : F) (n : ℕ) :
    qSeriesBar L F (f ^ n) = (qSeriesBar L F f) ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, qSeriesBar_mul, ih]


public theorem qSeriesBar_zpow (f : F) (n : ℤ) :
    qSeriesBar L F (f ^ n) = (qSeriesBar L F f) ^ n := by
  show ((f ^ n : F) : LaurentSeries L) = ((f : LaurentSeries L)) ^ n
  rw [← IntermediateField.algebraMap_apply (x := f ^ n),
    ← IntermediateField.algebraMap_apply (x := f), map_zpow₀]


@[simp] public theorem qSeriesBar_eq_zero_iff {f : F} : qSeriesBar L F f = 0 ↔ f = 0 :=
  ZeroMemClass.coe_eq_zero


public theorem qSeriesBar_ne_zero {f : F} (hf : f ≠ 0) : qSeriesBar L F f ≠ 0 :=
  fun h => hf (qSeriesBar_eq_zero_iff.mp h)


public theorem qSeriesBar_algebraMap (c : L) :
    qSeriesBar L F (algebraMap L F c) = HahnSeries.single (0 : ℤ) c := by
  have h : algebraMap L (LaurentSeries L) c
      = algebraMap F (LaurentSeries L) (algebraMap L F c) :=
    IsScalarTower.algebraMap_apply L F (LaurentSeries L) c
  rw [IntermediateField.algebraMap_apply] at h
  show ((algebraMap L F c : F) : LaurentSeries L) = _
  rw [← h, HahnSeries.algebraMap_apply', show algebraMap L (PowerSeries L) c = PowerSeries.C c by simp,
    HahnSeries.ofPowerSeries_C]
  rfl


public theorem order_qSeriesBar_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    (qSeriesBar L F (f * g)).order = (qSeriesBar L F f).order + (qSeriesBar L F g).order := by
  rw [qSeriesBar_mul]
  exact order_mul_of_ne_zero_bar (qSeriesBar_ne_zero hf) (qSeriesBar_ne_zero hg)

end QSeriesBar

section QAdicPlaceBar

variable (F : IntermediateField L (LaurentSeries L))


public theorem mem_qIntegersBar_iff {f : F} :
    f ∈ qIntegersBar L F ↔ 0 ≤ (qSeriesBar L F f).order := Iff.rfl

variable {L} in


public theorem isUnit_qIntegersBar_iff {x : qIntegersBar L F} (hx : (x : F) ≠ 0) :
    IsUnit x ↔ (qSeriesBar L F (x : F)).order = 0 := by
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : (x : F) * (b : F) = 1 := by
      have := congrArg (fun z : qIntegersBar L F => (z : F)) hb
      simpa using this
    have hbne : (b : F) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb'
      exact zero_ne_one hb'
    have hsum : (qSeriesBar L F (x : F)).order + (qSeriesBar L F (b : F)).order = 0 := by
      rw [← order_qSeriesBar_mul hx hbne, hb', qSeriesBar_one, HahnSeries.order_one]
    have h1 : (0 : ℤ) ≤ (qSeriesBar L F (x : F)).order := x.2
    have h2 : (0 : ℤ) ≤ (qSeriesBar L F (b : F)).order := b.2
    omega
  · intro h0
    have hinv : (x : F)⁻¹ ∈ qIntegersBar L F := by
      rw [mem_qIntegersBar_iff, qSeriesBar_inv,
        order_inv_of_ne_zero_bar (qSeriesBar_ne_zero hx)]
      omega
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : F)⁻¹, hinv⟩, ?_⟩
    refine Subtype.ext ?_
    push_cast
    exact mul_inv_cancel₀ hx

section Witness

variable {L} {j : F} (hj : (qSeriesBar L F j).order = -1)
include hj


public theorem ne_zero_of_order_eq_neg_one : j ≠ 0 := by
  rintro rfl
  rw [qSeriesBar_zero, HahnSeries.order_zero] at hj
  omega


public theorem notMem_qIntegersBar_of_order_eq_neg_one : j ∉ qIntegersBar L F := by
  rw [mem_qIntegersBar_iff, hj]
  omega


public theorem qIntegersBar_ne_top : qIntegersBar L F ≠ ⊤ := fun h =>
  notMem_qIntegersBar_of_order_eq_neg_one hj (h ▸ ValuationSubring.mem_top _)


public theorem order_inv_of_order_eq_neg_one : (qSeriesBar L F j⁻¹).order = 1 := by
  rw [qSeriesBar_inv, order_inv_of_ne_zero_bar (qSeriesBar_ne_zero (ne_zero_of_order_eq_neg_one hj)), hj]
  omega


public theorem inv_mem_qIntegersBar_of_order_eq_neg_one : j⁻¹ ∈ qIntegersBar L F := by
  rw [mem_qIntegersBar_iff, order_inv_of_order_eq_neg_one hj]
  omega


@[simp]
public theorem coe_uniformizerBar : ((uniformizerBar hj : qIntegersBar L F) : F) = j⁻¹ := rfl


public theorem uniformizerBar_ne_zero : ((uniformizerBar hj : qIntegersBar L F) : F) ≠ 0 :=
  inv_ne_zero (ne_zero_of_order_eq_neg_one hj)


public theorem irreducible_uniformizerBar : Irreducible (uniformizerBar hj) := by
  constructor
  · rw [isUnit_qIntegersBar_iff (uniformizerBar_ne_zero hj), coe_uniformizerBar,
      order_inv_of_order_eq_neg_one hj]
    omega
  · rintro a b hab
    have hab' : j⁻¹ = (a : F) * (b : F) := by
      have := congrArg (fun z : qIntegersBar L F => (z : F)) hab
      simpa using this
    have hj0 : j⁻¹ ≠ 0 := inv_ne_zero (ne_zero_of_order_eq_neg_one hj)
    have ha0 : (a : F) ≠ 0 := by
      intro h
      exact hj0 (by rw [hab', h, zero_mul])
    have hb0 : (b : F) ≠ 0 := by
      intro h
      exact hj0 (by rw [hab', h, mul_zero])
    have hsum : (qSeriesBar L F (a : F)).order + (qSeriesBar L F (b : F)).order = 1 := by
      rw [← order_qSeriesBar_mul ha0 hb0, ← hab', order_inv_of_order_eq_neg_one hj]
    have ha' : (0 : ℤ) ≤ (qSeriesBar L F (a : F)).order := a.2
    have hb' : (0 : ℤ) ≤ (qSeriesBar L F (b : F)).order := b.2
    rcases eq_or_lt_of_le ha' with ha0' | hapos
    · exact Or.inl ((isUnit_qIntegersBar_iff ha0).mpr ha0'.symm)
    rcases eq_or_lt_of_le hb' with hb0' | hbpos
    · exact Or.inr ((isUnit_qIntegersBar_iff hb0).mpr hb0'.symm)
    omega


public theorem qIntegersBar_isPrincipalIdealRing : IsPrincipalIdealRing (qIntegersBar L F) := by
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨uniformizerBar hj, irreducible_uniformizerBar hj, ?_⟩).toIsPrincipalIdealRing
  rintro x hx
  have hf : (x : F) ≠ 0 := fun h => hx (Subtype.ext h)
  have hmnonneg : (0 : ℤ) ≤ (qSeriesBar L F (x : F)).order := x.2
  set n : ℕ := (qSeriesBar L F (x : F)).order.toNat with hn
  have hmn : (n : ℤ) = (qSeriesBar L F (x : F)).order := Int.toNat_of_nonneg hmnonneg
  refine ⟨n, ?_⟩

  have hπ0 : j⁻¹ ≠ 0 := inv_ne_zero (ne_zero_of_order_eq_neg_one hj)
  have hπn : j⁻¹ ^ n ≠ 0 := pow_ne_zero _ hπ0
  have hdiv0 : (x : F) / j⁻¹ ^ n ≠ 0 := div_ne_zero hf hπn
  have hπorder : (qSeriesBar L F (j⁻¹ ^ n)).order = n := by
    rw [qSeriesBar_pow, order_pow_of_ne_zero_bar (qSeriesBar_ne_zero hπ0),
      order_inv_of_order_eq_neg_one hj, mul_one]
  have hu0 : (qSeriesBar L F ((x : F) / j⁻¹ ^ n)).order = 0 := by
    rw [div_eq_mul_inv, order_qSeriesBar_mul hf (inv_ne_zero hπn), qSeriesBar_inv,
      order_inv_of_ne_zero_bar (qSeriesBar_ne_zero hπn), hπorder, ← hmn]
    ring
  have humem : (x : F) / j⁻¹ ^ n ∈ qIntegersBar L F := by
    rw [mem_qIntegersBar_iff, hu0]
  have hu : IsUnit (⟨(x : F) / j⁻¹ ^ n, humem⟩ : qIntegersBar L F) :=
    (isUnit_qIntegersBar_iff hdiv0).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : qIntegersBar L F) : F) = (x : F) / j⁻¹ ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, coe_uniformizerBar, div_mul_cancel₀]
  exact hπn

end Witness

variable (F) in


@[simp]
public theorem qInftyPlaceBar_toValuationSubring (h : ∃ j : F, (qSeriesBar L F j).order = -1) :
    (qInftyPlaceBar L F h).toValuationSubring = qIntegersBar L F := rfl

end QAdicPlaceBar

section RationalTwin

variable (F : IntermediateField ℚ (LaurentSeries ℚ))


@[simp] public theorem qInftyPlaceRat_toValuationSubring (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) :
    (qInftyPlaceRat F h).toValuationSubring = qIntegersBar ℚ F := rfl

variable (N : ℕ) [NeZero N]


@[simp] public theorem cuspInfty_toValuationSubring :
    (cuspInfty N).toValuationSubring = qIntegersBar ℚ (modularFunctionField N) := rfl


public theorem jq_mem_full : jq ∈ modularFunctionFieldFull N :=
  modularFunctionField_le_full N (jq_mem N)


@[simp] public theorem cuspInftyFull_toValuationSubring :
    (cuspInftyFull N).toValuationSubring = qIntegersBar ℚ (modularFunctionFieldFull N) := rfl

end RationalTwin

section IsCusp

variable {K : Type*} {E : Type*} [Field K] [Field E] [Algebra K E]


public theorem isCusp_iff (j : E) (v : Place K E) : IsCusp j v ↔ j ∉ v.toValuationSubring := Iff.rfl

end IsCusp


public theorem isCusp_qInftyPlaceBar {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1)
    {j : F} (hj : (qSeriesBar L F j).order = -1) : IsCusp j (qInftyPlaceBar L F h) :=
  notMem_qIntegersBar_of_order_eq_neg_one hj


public theorem isCusp_qInftyPlaceRat {F : IntermediateField ℚ (LaurentSeries ℚ)} (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1)
    {j : F} (hj : (qSeriesBar ℚ F j).order = -1) : IsCusp j (qInftyPlaceRat F h) :=
  notMem_qIntegersBar_of_order_eq_neg_one hj


public theorem isCusp_cuspInfty (N : ℕ) [NeZero N] : IsCusp (⟨jq, jq_mem N⟩ : modularFunctionField N) (cuspInfty N) :=
  notMem_qIntegersBar_of_order_eq_neg_one order_jq


public theorem isCusp_cuspInftyFull (N : ℕ) [NeZero N] :
    IsCusp (⟨jq, jq_mem_full N⟩ : modularFunctionFieldFull N) (cuspInftyFull N) :=
  notMem_qIntegersBar_of_order_eq_neg_one order_jq

end ModularCurve

end
