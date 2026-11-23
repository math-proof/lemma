module

public import Mathlib
public import Theorem.UpperHalfPlane.XHDiamondModL
public import Theorem.LaurentSeries.QExpFrobeniusModL
public import Theorem.LaurentSeries.HeckeDifferential
public import Theorem.Set.PolarDifferentials
public import Theorem.WeierstrassCurve.SupersingularModuli
public import Theorem.CuspForm.TwoCuspLattice
public import Abbrev.ModularCurve_XHDifferentialsModL

public noncomputable section

set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve IntermediateField CongruenceSubgroup Set

open scoped MatrixGroups

namespace ModularCurve

section Supersingular

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ)

public theorem mem_ssPlacesQExp_iff (v : Place K (qExpFunctionFieldC K Γ)) :
    v ∈ ssPlacesQExp K Γ p ↔ IsSSPlaceQExp K Γ p v :=
  Iff.rfl


public theorem mem_ssPolarDifferentials_iff (ω : Ω[qExpFunctionFieldC K Γ⁄K]) :
    ω ∈ ssPolarDifferentials K Γ p ↔
      ∀ v : Place K (qExpFunctionFieldC K Γ),
        (v ∉ ssPlacesQExp K Γ p → v.IsRegularAt ω) ∧ (v ∈ ssPlacesQExp K Γ p → v.HasSimplePoleAt ω) :=
  Iff.rfl


public theorem regularDifferentials_le_ssPolarDifferentials :
    regularDifferentials K (qExpFunctionFieldC K Γ) ≤ ssPolarDifferentials K Γ p :=
  regularDifferentials_le_polarDifferentials _

end Supersingular

section Decimate

variable (K : Type*) [Field K] (p : ℕ) [NeZero p]

variable {K p} in

public theorem bddBelow_support_decimate (x : LaurentSeries K) :
    BddBelow (Function.support fun k : ℤ => x.coeff ((p : ℤ) * k)) := by
  by_cases hne : x.support.Nonempty
  · refine ⟨min (x.isWF_support.min hne) 0, fun k hk => ?_⟩
    have hk' : (p : ℤ) * k ∈ x.support := hk
    have hmin := x.isWF_support.min_le hne hk'
    have hp : (1 : ℤ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
    rcases le_or_gt 0 k with h0 | h0
    · exact (min_le_right _ _).trans h0
    · have : (p : ℤ) * k ≤ k := by nlinarith
      exact (min_le_left _ _).trans (hmin.trans this)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨0, fun k hk => ?_⟩
    exfalso
    have : (p : ℤ) * k ∈ x.support := hk
    rw [hne] at this
    exact this


@[simp]
public theorem coeff_qDecimate (x : LaurentSeries K) (k : ℤ) : (qDecimate K p x).coeff k = x.coeff ((p : ℤ) * k) := by
  simp only [qDecimate, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.coeff_ofSuppBddBelow]


public theorem qDecimate_qExpand (x : LaurentSeries K) : qDecimate K p (qExpand K p x) = x := by
  ext k
  rw [coeff_qDecimate, qExpand_coeff_mul]

end Decimate

section FrobPush

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [NeZero p]


public theorem isFrobPushDiff_frobPushDiffModL
    (h : ∃ C : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K], IsFrobPushDiff K Γ p C) :
    IsFrobPushDiff K Γ p (frobPushDiffModL K Γ p) := by
  rw [frobPushDiffModL, dif_pos h]
  exact h.choose_spec


public theorem frobPushDiffModL_of_not
    (h : ¬ ∃ C : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K], IsFrobPushDiff K Γ p C) :
    frobPushDiffModL K Γ p = 0 := by
  rw [frobPushDiffModL, dif_neg h]


public theorem IsFrobPushDiff.eq_of_injective {C C' : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K]}
    (hC : IsFrobPushDiff K Γ p C) (hC' : IsFrobPushDiff K Γ p C')
    (hinj : Function.Injective (diffQExp (qExpFunctionFieldC K Γ))) : C = C' := by
  refine LinearMap.ext fun ω => hinj ?_
  rw [hC ω, hC' ω]

end FrobPush

section HeckeDiff

variable (K : Type*) [Field K] (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]


@[simp]
public theorem coe_heckeAlphaModLH (x : qExpFunctionFieldC K (CohCarrier.GammaH N H')) :
    (heckeAlphaModLH K N H' ℓ x : LaurentSeries K) = (x : LaurentSeries K) :=
  IntermediateField.coe_inclusion _ x


@[simp]
public theorem coe_heckeBetaModLHOf (h : HeckeBetaModLHDefined K N H' ℓ)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH N H')) :
    (heckeBetaModLHOf K N H' ℓ h x : LaurentSeries K) = qExpand K ℓ (x : LaurentSeries K) :=
  rfl

open Classical in


public theorem heckeBetaModLH_eq (h : HeckeBetaModLHDefined K N H' ℓ) :
    heckeBetaModLH K N H' ℓ = heckeBetaModLHOf K N H' ℓ h := by
  rw [heckeBetaModLH, dif_pos h]


public theorem heckeBetaModLH_of_not (h : ¬ HeckeBetaModLHDefined K N H' ℓ) :
    heckeBetaModLH K N H' ℓ = heckeAlphaModLH K N H' ℓ := by
  rw [heckeBetaModLH, dif_neg h]


public theorem coe_heckeBetaModLH (h : HeckeBetaModLHDefined K N H' ℓ)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH N H')) :
    (heckeBetaModLH K N H' ℓ x : LaurentSeries K) = qExpand K ℓ (x : LaurentSeries K) := by
  rw [heckeBetaModLH_eq K N H' ℓ h, coe_heckeBetaModLHOf]


public theorem heckeDiffModLH_apply (ω : Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) :
    heckeDiffModLH K N H' ℓ ω =
      Differential.traceAlong (heckeBetaModLH K N H' ℓ)
        (Differential.pullbackAlong (heckeAlphaModLH K N H' ℓ) ω) :=
  rfl

end HeckeDiff

section DiamondDiff

variable (K : Type*) [Field K] (N : ℕ) (H' : Subgroup (ZMod N)ˣ)

open Classical in


public theorem isDiamondPullbackModL_diamondActionModL
    (h : ∃ ρ : Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H') ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H')),
      IsDiamondPullbackModL K N H' ρ) :
    IsDiamondPullbackModL K N H' (diamondActionModL K N H') := by
  rw [diamondActionModL, dif_pos h]
  exact h.choose_spec


public theorem diamondActionModL_of_not
    (h : ¬ ∃ ρ : Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H') ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H')),
      IsDiamondPullbackModL K N H' ρ) :
    diamondActionModL K N H' = 1 := by
  rw [diamondActionModL, dif_neg h]

variable (K N H')
variable [NeZero N]


public theorem diamondDiffModLH_apply (d : (ZMod N)ˣ) (ω : Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) :
    diamondDiffModLH K N H' d ω =
      Differential.pullbackAlong (diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)).toAlgHom ω :=
  rfl

end DiamondDiff

section GenFamily

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)


public theorem mem_infSubgroup_iff (u : (ZMod (M / p))ˣ) :
    u ∈ infSubgroup p M H hpM ↔ ∃ d ∈ H, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d = u :=
  Subgroup.mem_map

omit [Fact p.Prime] [NeZero M] in

public theorem unitsMap_mem_infSubgroup {d : (ZMod M)ˣ} (hd : d ∈ H) :
    ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ infSubgroup p M H hpM :=
  Subgroup.mem_map_of_mem _ hd

include hpM in


public theorem neZero_div : NeZero (M / p) :=
  ⟨(Nat.div_ne_zero_iff_of_dvd hpM).mpr ⟨NeZero.ne M, (Fact.out : p.Prime).ne_zero⟩⟩

variable (S : Set ℕ)


public theorem genDiffModL_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) :
    genDiffModL K p M H hpM S (.T ℓ hℓ hℓS hℓM) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeDiffModLH K (M / p) (infSubgroup p M H hpM) ℓ) :=
  rfl


public theorem genDiffModL_U_self (hp : p.Prime) (hpM' : p ∣ M) :
    genDiffModL K p M H hpM S (.U p hp hpM') =
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
        frobPushDiffModL K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p) := by
  simp only [genDiffModL, if_true]


public theorem genDiffModL_U_of_ne (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p) :
    genDiffModL K p M H hpM S (.U q hq hqM) =
      (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeDiffModLH K (M / p) (infSubgroup p M H hpM) q) := by
  simp only [genDiffModL, if_neg hqp]


public theorem genDiffModL_dia (d : (ZMod M)ˣ) :
    genDiffModL K p M H hpM S (.dia d) =
      (haveI : NeZero (M / p) := neZero_div p M hpM;
        diamondDiffModLH K (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)) :=
  rfl

end GenFamily

section TwoComponent

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime] [CharP K p]


public theorem mem_ssNodePairsQExp_iff (s : Place K (qExpFunctionFieldC K Γ) × Place K (qExpFunctionFieldC K Γ)) :
    s ∈ ssNodePairsQExp K Γ p ↔ s.2 ∈ ssPlacesQExp K Γ p ∧ s.1 = qExpFrobeniusPlaceModL K Γ p s.2 :=
  Iff.rfl

variable {K Γ p} in

public theorem frob_mk_mem_ssNodePairsQExp {y : Place K (qExpFunctionFieldC K Γ)} (hy : y ∈ ssPlacesQExp K Γ p) :
    (qExpFrobeniusPlaceModL K Γ p y, y) ∈ ssNodePairsQExp K Γ p :=
  ⟨hy, rfl⟩


@[simp]
public theorem pairUpModL_apply (C : V →ₗ[K] V) (ω : V × V) : pairUpModL C ω = (C ω.1, -ω.1) :=
  rfl


@[simp]
public theorem pairDiagModL_apply (T : V →ₗ[K] V) (ω : V × V) : pairDiagModL T ω = (T ω.1, T ω.2) :=
  rfl

end PairOperators

section GenPair

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (S : Set ℕ)


public theorem natCast_mem_intIdeal : (p : (⊥ : Subring ℂ)) ∈ intIdeal p :=
  Ideal.subset_span rfl


public theorem IntTwoCuspForms.nsmul_eq_zero (x : IntTwoCuspForms M H p) : p • x = 0 := by
  change p • (x : TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) = 0
  obtain ⟨y, rfl⟩ := twoCuspReduce_surjective M H 2 p (⊥ : Subring ℂ) (intIdeal p) x
  have h : p • twoCuspReduce (intIdeal p) y = twoCuspReduce (intIdeal p) (p • y) :=
    (map_nsmul (twoCuspReduce (M := M) (H := H) (k := 2) (p := p) (A := (⊥ : Subring ℂ)) (intIdeal p)) p y).symm
  refine h.trans ((twoCuspReduce_eq_zero_iff (M := M) (H := H) (k := 2) (p := p) (A := (⊥ : Subring ℂ))
    (intIdeal p) (p • y)).mpr ?_)
  rw [← Nat.cast_smul_eq_nsmul (⊥ : Subring ℂ)]
  exact Submodule.smul_mem_smul (natCast_mem_intIdeal p) Submodule.mem_top

variable [Fact p.Prime]

omit [Fact p.Prime] in


public theorem intTwoCuspReduce_apply (x : twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    intTwoCuspReduce M H p x = (twoCuspReduce (intIdeal p) x : TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) :=
  rfl

omit [Fact p.Prime] in

public theorem intTwoCuspReduce_surjective : Function.Surjective (intTwoCuspReduce M H p) :=
  twoCuspReduce_surjective M H 2 p (⊥ : Subring ℂ) (intIdeal p)

omit [Fact p.Prime] in


public theorem intTwoCuspGenMod_apply (S : Set ℕ) (g : CohCarrier.Gen M S) (x : IntTwoCuspForms M H p) :
    intTwoCuspGenMod M H p S g x =
      (twoCuspGenMod (intIdeal p) S g (x : TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) :
        TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) :=
  rfl


public theorem intTwoCuspGenMod_reduce (S : Set ℕ) (g : CohCarrier.Gen M S)
    (x : twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    intTwoCuspGenMod M H p S g (intTwoCuspReduce M H p x) =
      intTwoCuspReduce M H p (twoCuspEnd ⟨heckeGenH S 2 g, heckeGenH_mem_heckeRingH S 2 g⟩ x) :=
  rfl

end CuspForm

namespace ModularCurve

open scoped TensorProduct

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  [Algebra (ZMod p) K]


public theorem IsInfReductionMap.diffQExp_apply
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
      Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K]}
    (hρ : IsInfReductionMap K p M H hpM ρ) {f : CuspForm (CohCarrier.GammaH M H) 2}
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) {pf : PowerSeries ℤ}
    (hpf : IsIntegralQExp f pf) :
    diffQExp (qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))
        (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) =
      intSeriesC K pf :=
  hρ f hf pf hpf

end ModularCurve

end
