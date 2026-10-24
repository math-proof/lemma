import Mathlib
import Lemma.Definitions.Def_ModularCurve_QAdicPlace
import Lemma.Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_of_lt

set_option autoImplicit false

noncomputable section

open HahnSeries AlgebraicCurve

set_option synthInstance.maxHeartbeats 400000

namespace ModularCurve

variable (K : Type*) [Field K]

section OrderJqModC

theorem jqModC_ne_zero_def : jqModC K ≠ 0 := by
  intro h
  have h1 : (jqModC K).coeff (-1 : ℤ) = 1 := coeff_jqModC_neg_one K
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

theorem order_jqModC_def : (jqModC K).order = -1 := by
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [coeff_jqModC_neg_one]
    exact one_ne_zero
  · by_contra hlt
    rw [not_le] at hlt
    refine HahnSeries.coeff_order_eq_zero.not.mpr (jqModC_ne_zero_def K) ?_
    have h := coeff_jqModC_pow_of_lt K (b := 1) (m := (jqModC K).order)
      (by simpa using hlt)
    simpa using h

theorem order_qExpandC (p : ℕ) [NeZero p] {f : LaurentSeries K} (hf : f ≠ 0) :
    (qExpand K p f).order = (p : ℤ) * f.order := by
  have hp : (0 : ℤ) < (p : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hcoeff : (qExpand K p f).coeff ((p : ℤ) * f.order) = f.coeff f.order := by
    rw [qExpand_coeff_mul]
  have hcoeff' : (qExpand K p f).coeff ((p : ℤ) * f.order) ≠ 0 := by
    rw [hcoeff]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hf
  have hne : qExpand K p f ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hcoeff'
  have hbelow : ∀ k : ℤ, k < (p : ℤ) * f.order → (qExpand K p f).coeff k = 0 := by
    intro k hk
    by_cases hdvd : (p : ℤ) ∣ k
    · obtain ⟨j, rfl⟩ := hdvd
      rw [qExpand_coeff_mul]
      exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_mul_lt_mul_left hk hp.le)
    · exact qExpand_coeff_of_not_dvd p f hdvd
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hcoeff') ?_
  by_contra hlt
  rw [not_le] at hlt
  exact hne (HahnSeries.coeff_order_eq_zero.mp (hbelow _ hlt))

theorem jqNModC_ne_zero (N : ℕ) [NeZero N] : jqNModC K N ≠ 0 := by
  intro h
  have := order_qExpandC K N (jqModC_ne_zero_def K)
  rw [show qExpand K N (jqModC K) = jqNModC K N from rfl, h, HahnSeries.order_zero,
    order_jqModC_def] at this
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  omega

theorem order_jqNModC (N : ℕ) [NeZero N] : (jqNModC K N).order = -(N : ℤ) := by
  rw [show jqNModC K N = qExpand K N (jqModC K) from rfl,
    order_qExpandC K N (jqModC_ne_zero_def K), order_jqModC_def]
  ring

end OrderJqModC

section QAdicPlaceMod

variable (F : IntermediateField K (LaurentSeries K))

variable {F} in

def jModElt (hF : jqModC K ∈ F) : F := ⟨jqModC K, hF⟩

variable {F} in
@[simp]
theorem qSeriesBar_jModElt (hF : jqModC K ∈ F) :
    qSeriesBar K F (jModElt K hF) = jqModC K := rfl

variable {F} in
theorem jModElt_ne_zero (hF : jqModC K ∈ F) : jModElt K hF ≠ 0 := by
  intro h
  exact jqModC_ne_zero_def K (by simpa [jModElt, Subtype.ext_iff] using h)

variable {F} in

theorem jModElt_notMem_qIntegersBar (hF : jqModC K ∈ F) :
    jModElt K hF ∉ qIntegersBar K F := by
  rw [mem_qIntegersBar_iff, qSeriesBar_jModElt, order_jqModC_def]
  omega

variable {F} in
theorem qIntegersBar_ne_top_of_jqModC_mem (hF : jqModC K ∈ F) : qIntegersBar K F ≠ ⊤ := by
  intro h
  exact jModElt_notMem_qIntegersBar K hF (h ▸ ValuationSubring.mem_top _)

variable {F} in

def jModInvElt (hF : jqModC K ∈ F) : F := (jModElt K hF)⁻¹

variable {F} in
theorem qSeriesBar_jModInvElt (hF : jqModC K ∈ F) :
    qSeriesBar K F (jModInvElt K hF) = (jqModC K)⁻¹ := by
  rw [jModInvElt, qSeriesBar_inv, qSeriesBar_jModElt]

variable {F} in
theorem jModInvElt_ne_zero (hF : jqModC K ∈ F) : jModInvElt K hF ≠ 0 :=
  inv_ne_zero (jModElt_ne_zero K hF)

variable {F} in

theorem order_jModInvElt (hF : jqModC K ∈ F) :
    (qSeriesBar K F (jModInvElt K hF)).order = 1 := by
  rw [qSeriesBar_jModInvElt, order_inv_of_ne_zero_bar (jqModC_ne_zero_def K), order_jqModC_def]
  omega

variable {F} in
theorem jModInvElt_mem_qIntegersBar (hF : jqModC K ∈ F) :
    jModInvElt K hF ∈ qIntegersBar K F := by
  rw [mem_qIntegersBar_iff, order_jModInvElt]
  omega

variable {F} in

def uniformizerMod (hF : jqModC K ∈ F) : qIntegersBar K F :=
  ⟨jModInvElt K hF, jModInvElt_mem_qIntegersBar K hF⟩

variable {F} in
@[simp]
theorem coe_uniformizerMod (hF : jqModC K ∈ F) :
    ((uniformizerMod K hF : qIntegersBar K F) : F) = jModInvElt K hF := rfl

variable {F} in
theorem uniformizerMod_ne_zero (hF : jqModC K ∈ F) :
    ((uniformizerMod K hF : qIntegersBar K F) : F) ≠ 0 :=
  jModInvElt_ne_zero K hF

variable {F} in

theorem irreducible_uniformizerMod (hF : jqModC K ∈ F) :
    Irreducible (uniformizerMod K hF) := by
  constructor
  · rw [isUnit_qIntegersBar_iff (uniformizerMod_ne_zero K hF), coe_uniformizerMod,
      order_jModInvElt]
    omega
  · rintro a b hab
    have hab' : jModInvElt K hF = (a : F) * (b : F) := by
      have := congrArg (fun z : qIntegersBar K F => (z : F)) hab
      simpa using this
    have ha0 : (a : F) ≠ 0 := by
      intro h
      exact jModInvElt_ne_zero K hF (by rw [hab', h, zero_mul])
    have hb0 : (b : F) ≠ 0 := by
      intro h
      exact jModInvElt_ne_zero K hF (by rw [hab', h, mul_zero])
    have hsum : (qSeriesBar K F (a : F)).order + (qSeriesBar K F (b : F)).order = 1 := by
      rw [← order_qSeriesBar_mul ha0 hb0, ← hab', order_jModInvElt]
    have ha' : (0 : ℤ) ≤ (qSeriesBar K F (a : F)).order := a.2
    have hb' : (0 : ℤ) ≤ (qSeriesBar K F (b : F)).order := b.2
    rcases eq_or_lt_of_le ha' with ha0' | hapos
    · exact Or.inl ((isUnit_qIntegersBar_iff ha0).mpr ha0'.symm)
    rcases eq_or_lt_of_le hb' with hb0' | hbpos
    · exact Or.inr ((isUnit_qIntegersBar_iff hb0).mpr hb0'.symm)
    omega

variable {F} in

theorem qIntegersBar_isPrincipalIdealRing_of_jqModC_mem (hF : jqModC K ∈ F) :
    IsPrincipalIdealRing (qIntegersBar K F) := by
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨uniformizerMod K hF, irreducible_uniformizerMod K hF, ?_⟩).toIsPrincipalIdealRing
  rintro x hx
  have hf : (x : F) ≠ 0 := fun h => hx (Subtype.ext h)
  have hmnonneg : (0 : ℤ) ≤ (qSeriesBar K F (x : F)).order := x.2
  set n : ℕ := (qSeriesBar K F (x : F)).order.toNat with hn
  have hmn : (n : ℤ) = (qSeriesBar K F (x : F)).order := Int.toNat_of_nonneg hmnonneg
  refine ⟨n, ?_⟩
  have hπn : (jModInvElt K hF) ^ n ≠ 0 := pow_ne_zero _ (jModInvElt_ne_zero K hF)
  have hdiv0 : (x : F) / (jModInvElt K hF) ^ n ≠ 0 := div_ne_zero hf hπn
  have hπorder : (qSeriesBar K F ((jModInvElt K hF) ^ n)).order = n := by
    rw [qSeriesBar_pow, order_pow_of_ne_zero_bar (qSeriesBar_ne_zero (jModInvElt_ne_zero K hF)),
      order_jModInvElt, mul_one]
  have hu0 : (qSeriesBar K F ((x : F) / (jModInvElt K hF) ^ n)).order = 0 := by
    rw [div_eq_mul_inv, order_qSeriesBar_mul hf (inv_ne_zero hπn), qSeriesBar_inv,
      order_inv_of_ne_zero_bar (qSeriesBar_ne_zero hπn), hπorder, ← hmn]
    ring
  have humem : (x : F) / (jModInvElt K hF) ^ n ∈ qIntegersBar K F := by
    rw [mem_qIntegersBar_iff, hu0]
  have hu : IsUnit (⟨(x : F) / (jModInvElt K hF) ^ n, humem⟩ : qIntegersBar K F) :=
    (isUnit_qIntegersBar_iff hdiv0).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : qIntegersBar K F) : F) = (x : F) / (jModInvElt K hF) ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, coe_uniformizerMod, div_mul_cancel₀]
  exact hπn

variable {F} in

def qInftyPlaceMod (hF : jqModC K ∈ F) : Place K F where
  toValuationSubring := qIntegersBar K F
  algebraMap_mem' := fun a => by
    rw [mem_qIntegersBar_iff, qSeriesBar_algebraMap]
    rcases eq_or_ne a 0 with rfl | ha
    · simp only [HahnSeries.single_eq_zero, HahnSeries.order_zero, le_refl]
    · rw [HahnSeries.order_single ha]
  ne_top' := qIntegersBar_ne_top_of_jqModC_mem K hF
  isPrincipalIdealRing' := qIntegersBar_isPrincipalIdealRing_of_jqModC_mem K hF

variable {F} in
@[simp]
theorem qInftyPlaceMod_toValuationSubring (hF : jqModC K ∈ F) :
    (qInftyPlaceMod K hF).toValuationSubring = qIntegersBar K F := rfl

variable {F} in

theorem ord_qInftyPlaceMod (hF : jqModC K ∈ F) (f : F) :
    (qInftyPlaceMod K hF).ord f = (qSeriesBar K F f).order := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [Place.ord_zero, qSeriesBar_zero, HahnSeries.order_zero]
  set n : ℤ := (qSeriesBar K F f).order with hn
  have hjn : (jModInvElt K hF) ^ n ≠ 0 := zpow_ne_zero _ (jModInvElt_ne_zero K hF)
  have huord : (qSeriesBar K F (f / (jModInvElt K hF) ^ n)).order = 0 := by
    rw [qSeriesBar_div, qSeriesBar_zpow,
      order_div_of_ne_zero_bar (qSeriesBar_ne_zero hf)
        (zpow_ne_zero _ (qSeriesBar_ne_zero (jModInvElt_ne_zero K hF))),
      order_zpow_of_ne_zero_bar (qSeriesBar_ne_zero (jModInvElt_ne_zero K hF)),
      order_jModInvElt, mul_one, ← hn]
    ring
  have humem : f / (jModInvElt K hF) ^ n ∈ qIntegersBar K F := by
    rw [mem_qIntegersBar_iff, huord]
  have hune : f / (jModInvElt K hF) ^ n ≠ 0 := div_ne_zero hf hjn
  have huu : IsUnit (⟨f / (jModInvElt K hF) ^ n, humem⟩ : qIntegersBar K F) :=
    (isUnit_qIntegersBar_iff hune).mpr huord
  have hdecomp : f = ((huu.unit : qIntegersBar K F) : F)
      * (((uniformizerMod K hF : qIntegersBar K F) : F) ^ n) := by
    have hcoe : ((huu.unit : qIntegersBar K F) : F) = f / (jModInvElt K hF) ^ n := by
      rw [IsUnit.unit_spec]
    rw [hcoe, coe_uniformizerMod]
    exact (div_mul_cancel₀ f hjn).symm
  rw [hdecomp]
  exact (qInftyPlaceMod K hF).ord_unit_smul_zpow huu.unit (irreducible_uniformizerMod K hF) n

variable {F} in

theorem algebraMap_coeff_zero_sub_not_isUnit_mod (hF : jqModC K ∈ F)
    (f : (qInftyPlaceMod K hF).toValuationSubring) :
    ¬IsUnit (algebraMap K (qInftyPlaceMod K hF).toValuationSubring
      ((qSeriesBar K F (f : F)).coeff 0) - f) := by
  set c : K := (qSeriesBar K F (f : F)).coeff 0 with hc
  have hcoe : qSeriesBar K F
      ((algebraMap K (qInftyPlaceMod K hF).toValuationSubring c - f : _) : F)
      = HahnSeries.single (0 : ℤ) c - qSeriesBar K F (f : F) := by
    have h1 : ((algebraMap K (qInftyPlaceMod K hF).toValuationSubring c - f : _) : F)
        = algebraMap K F c - (f : F) := by
      push_cast
      rw [Place.coe_algebraMap]
    rw [h1, qSeriesBar_sub, qSeriesBar_algebraMap]
  have hgcoeff : ∀ k : ℤ, k ≤ 0 →
      (qSeriesBar K F
        ((algebraMap K (qInftyPlaceMod K hF).toValuationSubring c - f : _) : F)).coeff k
        = 0 := by
    intro k hk
    rw [hcoe, HahnSeries.coeff_sub]
    rcases lt_or_eq_of_le hk with hk' | hk'
    · rw [HahnSeries.coeff_single_of_ne (by omega : k ≠ 0),
        HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk' f.2), sub_zero]
    · subst hk'
      rw [HahnSeries.coeff_single_same, hc, sub_self]
  intro hunit
  rcases eq_or_ne
    (((algebraMap K (qInftyPlaceMod K hF).toValuationSubring c - f : _) : F)) 0
    with hg0 | hg0
  · have hzero : (algebraMap K (qInftyPlaceMod K hF).toValuationSubring c - f : _) = 0 :=
      Subtype.ext hg0
    rw [hzero] at hunit
    exact not_isUnit_zero hunit
  · have horder := (isUnit_qIntegersBar_iff hg0).mp hunit
    have hne := HahnSeries.coeff_order_eq_zero.not.mpr (qSeriesBar_ne_zero hg0)
    rw [horder] at hne
    exact hne (hgcoeff 0 le_rfl)

variable {F} in

theorem surjective_algebraMap_residueField_mod (hF : jqModC K ∈ F) :
    Function.Surjective (algebraMap K (qInftyPlaceMod K hF).ResidueField) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := IsLocalRing.maximalIdeal (qInftyPlaceMod K hF).toValuationSubring) y
  refine ⟨(qSeriesBar K F (f : F)).coeff 0, ?_⟩
  have hmem : algebraMap K (qInftyPlaceMod K hF).toValuationSubring
      ((qSeriesBar K F (f : F)).coeff 0) - f ∈
      IsLocalRing.maximalIdeal (qInftyPlaceMod K hF).toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact algebraMap_coeff_zero_sub_not_isUnit_mod K hF f
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := IsLocalRing.maximalIdeal (qInftyPlaceMod K hF).toValuationSubring)
    (algebraMap K (qInftyPlaceMod K hF).toValuationSubring
      ((qSeriesBar K F (f : F)).coeff 0)) f).mpr hmem

variable {F} in

theorem deg_qInftyPlaceMod (hF : jqModC K ∈ F) : (qInftyPlaceMod K hF).deg = 1 := by
  have hsurj := surjective_algebraMap_residueField_mod K hF
  have hinj : Function.Injective (algebraMap K (qInftyPlaceMod K hF).ResidueField) :=
    (algebraMap K (qInftyPlaceMod K hF).ResidueField).injective
  have e : K ≃ₐ[K] (qInftyPlaceMod K hF).ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId K _) ⟨hinj, hsurj⟩
  show Module.finrank K (qInftyPlaceMod K hF).ResidueField = 1
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

end QAdicPlaceMod

section LevelN

variable (N : ℕ) [NeZero N]

def cuspInftyGeom : Place K (modularFunctionFieldC K N) :=
  qInftyPlaceMod K (jqModC_mem K N)

theorem nonempty_place_modularFunctionFieldC :
    Nonempty (Place K (modularFunctionFieldC K N)) :=
  ⟨cuspInftyGeom K N⟩

theorem ord_cuspInftyGeom_jq :
    (cuspInftyGeom K N).ord ⟨jqModC K, jqModC_mem K N⟩ = -1 := by
  rw [cuspInftyGeom, ord_qInftyPlaceMod]
  exact order_jqModC_def K

theorem ord_cuspInftyGeom_jqN :
    (cuspInftyGeom K N).ord ⟨jqNModC K N, jqNModC_mem K N⟩ = -(N : ℤ) := by
  rw [cuspInftyGeom, ord_qInftyPlaceMod]
  exact order_jqNModC K N

theorem deg_cuspInftyGeom : (cuspInftyGeom K N).deg = 1 :=
  deg_qInftyPlaceMod K (jqModC_mem K N)

end LevelN

section Gates

theorem gate_ord_cuspInftyGeom_fbar_two :
    (cuspInftyGeom (AlgebraicClosure (ZMod 2)) 3).ord
      ⟨jqModC _, jqModC_mem _ 3⟩ = -1 :=
  ord_cuspInftyGeom_jq _ 3

theorem gate_ord_cuspInftyGeom_fbar_two_ne_zero :
    (cuspInftyGeom (AlgebraicClosure (ZMod 2)) 3).ord
      ⟨jqModC _, jqModC_mem _ 3⟩ ≠ 0 := by
  rw [gate_ord_cuspInftyGeom_fbar_two]
  omega

end Gates

end ModularCurve
