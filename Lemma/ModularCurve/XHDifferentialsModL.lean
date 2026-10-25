import Mathlib
import Lemma.ModularCurve.XHDiamondModL
import Lemma.ModularCurve.QExpFrobeniusModL
import Lemma.ModularCurve.HeckeDifferential
import Lemma.AlgebraicCurve.PolarDifferentials
import Lemma.ModularCurve.SupersingularModuli
import Lemma.CuspForm.TwoCuspLattice
import Instance.ModularCurve_XHDifferentialsModL
import Abbrev.ModularCurve_XHDifferentialsModL

set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve IntermediateField CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

section Supersingular

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ)

def IsSSPlaceQExp (v : Place K (qExpFunctionFieldC K Γ)) : Prop :=
  ∃ (x : qExpFunctionFieldC K Γ) (a : K), (x : LaurentSeries K) = jqModC K ∧ v.HasValue x a ∧
    a ∈ @ssJSet p K _ (Classical.decEq K)

def ssPlacesQExp : Set (Place K (qExpFunctionFieldC K Γ)) :=
  {v | IsSSPlaceQExp K Γ p v}

variable {K Γ p} in
theorem mem_ssPlacesQExp_iff (v : Place K (qExpFunctionFieldC K Γ)) :
    v ∈ ssPlacesQExp K Γ p ↔ IsSSPlaceQExp K Γ p v :=
  Iff.rfl

def ssPolarDifferentials : Submodule K Ω[qExpFunctionFieldC K Γ⁄K] :=
  polarDifferentials K (qExpFunctionFieldC K Γ) (ssPlacesQExp K Γ p)

variable {K Γ p} in
theorem mem_ssPolarDifferentials_iff (ω : Ω[qExpFunctionFieldC K Γ⁄K]) :
    ω ∈ ssPolarDifferentials K Γ p ↔
      ∀ v : Place K (qExpFunctionFieldC K Γ),
        (v ∉ ssPlacesQExp K Γ p → v.IsRegularAt ω) ∧ (v ∈ ssPlacesQExp K Γ p → v.HasSimplePoleAt ω) :=
  Iff.rfl

theorem regularDifferentials_le_ssPolarDifferentials :
    regularDifferentials K (qExpFunctionFieldC K Γ) ≤ ssPolarDifferentials K Γ p :=
  regularDifferentials_le_polarDifferentials _

end Supersingular

section Decimate

variable (K : Type*) [Field K] (p : ℕ) [NeZero p]

variable {K p} in
private theorem bddBelow_support_decimate (x : LaurentSeries K) :
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

def qDecimate : LaurentSeries K →ₗ[K] LaurentSeries K where
  toFun x := HahnSeries.ofSuppBddBelow (fun k : ℤ => x.coeff ((p : ℤ) * k)) (bddBelow_support_decimate x)
  map_add' x y := by
    ext k
    simp only [HahnSeries.coeff_ofSuppBddBelow, HahnSeries.coeff_add]
  map_smul' c x := by
    ext k
    simp only [HahnSeries.coeff_ofSuppBddBelow, HahnSeries.coeff_smul, RingHom.id_apply]

@[simp]
theorem coeff_qDecimate (x : LaurentSeries K) (k : ℤ) : (qDecimate K p x).coeff k = x.coeff ((p : ℤ) * k) := by
  simp only [qDecimate, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.coeff_ofSuppBddBelow]

theorem qDecimate_qExpand (x : LaurentSeries K) : qDecimate K p (qExpand K p x) = x := by
  ext k
  rw [coeff_qDecimate, qExpand_coeff_mul]

end Decimate

section FrobPush

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [NeZero p]

def IsFrobPushDiff (C : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K]) : Prop :=
  ∀ ω : Ω[qExpFunctionFieldC K Γ⁄K],
    diffQExp (qExpFunctionFieldC K Γ) (C ω) = qDecimate K p (diffQExp (qExpFunctionFieldC K Γ) ω)

open Classical in

def frobPushDiffModL : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K] :=
  if h : ∃ C : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K], IsFrobPushDiff K Γ p C
  then h.choose else 0

variable {K Γ p}

theorem isFrobPushDiff_frobPushDiffModL
    (h : ∃ C : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K], IsFrobPushDiff K Γ p C) :
    IsFrobPushDiff K Γ p (frobPushDiffModL K Γ p) := by
  rw [frobPushDiffModL, dif_pos h]
  exact h.choose_spec

theorem frobPushDiffModL_of_not
    (h : ¬ ∃ C : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K], IsFrobPushDiff K Γ p C) :
    frobPushDiffModL K Γ p = 0 := by
  rw [frobPushDiffModL, dif_neg h]

theorem IsFrobPushDiff.eq_of_injective {C C' : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K]}
    (hC : IsFrobPushDiff K Γ p C) (hC' : IsFrobPushDiff K Γ p C')
    (hinj : Function.Injective (diffQExp (qExpFunctionFieldC K Γ))) : C = C' := by
  refine LinearMap.ext fun ω => hinj ?_
  rw [hC ω, hC' ω]

end FrobPush

section HeckeDiff

variable (K : Type*) [Field K] (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]

def heckeAlphaModLH :
    qExpFunctionFieldC K (CohCarrier.GammaH N H') →ₐ[K]
      qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) :=
  IntermediateField.inclusion (qExpFunctionFieldC_mono K inf_le_left)

omit [NeZero ℓ] in
@[simp]
theorem coe_heckeAlphaModLH (x : qExpFunctionFieldC K (CohCarrier.GammaH N H')) :
    (heckeAlphaModLH K N H' ℓ x : LaurentSeries K) = (x : LaurentSeries K) :=
  IntermediateField.coe_inclusion _ x

def HeckeBetaModLHDefined : Prop :=
  ∀ y ∈ qExpFunctionFieldC K (CohCarrier.GammaH N H'),
    qExpand K ℓ y ∈ qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ))

def heckeBetaModLHOf (h : HeckeBetaModLHDefined K N H' ℓ) :
    qExpFunctionFieldC K (CohCarrier.GammaH N H') →ₐ[K]
      qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) where
  toFun x := ⟨qExpand K ℓ (x : LaurentSeries K), h x x.2⟩
  map_one' := Subtype.ext (map_one (qExpand K ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand K ℓ) _ _)
  commutes' a := Subtype.ext <| by
    show qExpand K ℓ (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

@[simp]
theorem coe_heckeBetaModLHOf (h : HeckeBetaModLHDefined K N H' ℓ)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH N H')) :
    (heckeBetaModLHOf K N H' ℓ h x : LaurentSeries K) = qExpand K ℓ (x : LaurentSeries K) :=
  rfl

open Classical in

def heckeBetaModLH :
    qExpFunctionFieldC K (CohCarrier.GammaH N H') →ₐ[K]
      qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) :=
  if h : HeckeBetaModLHDefined K N H' ℓ then heckeBetaModLHOf K N H' ℓ h else heckeAlphaModLH K N H' ℓ

theorem heckeBetaModLH_eq (h : HeckeBetaModLHDefined K N H' ℓ) :
    heckeBetaModLH K N H' ℓ = heckeBetaModLHOf K N H' ℓ h := by
  rw [heckeBetaModLH, dif_pos h]

theorem heckeBetaModLH_of_not (h : ¬ HeckeBetaModLHDefined K N H' ℓ) :
    heckeBetaModLH K N H' ℓ = heckeAlphaModLH K N H' ℓ := by
  rw [heckeBetaModLH, dif_neg h]

theorem coe_heckeBetaModLH (h : HeckeBetaModLHDefined K N H' ℓ)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH N H')) :
    (heckeBetaModLH K N H' ℓ x : LaurentSeries K) = qExpand K ℓ (x : LaurentSeries K) := by
  rw [heckeBetaModLH_eq K N H' ℓ h, coe_heckeBetaModLHOf]

def heckeDiffModLH :
    Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] →ₗ[K] Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] :=
  Differential.correspondence (heckeBetaModLH K N H' ℓ) (heckeAlphaModLH K N H' ℓ)

theorem heckeDiffModLH_apply (ω : Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) :
    heckeDiffModLH K N H' ℓ ω =
      Differential.traceAlong (heckeBetaModLH K N H' ℓ)
        (Differential.pullbackAlong (heckeAlphaModLH K N H' ℓ) ω) :=
  rfl

end HeckeDiff

section DiamondDiff

variable (K : Type*) [Field K] (N : ℕ) (H' : Subgroup (ZMod N)ˣ)

open Classical in

def diamondActionModL :
    Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H') ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H')) :=
  if h : ∃ ρ : Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H') ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H')),
      IsDiamondPullbackModL K N H' ρ
  then h.choose else 1

variable {K N H'}

theorem isDiamondPullbackModL_diamondActionModL
    (h : ∃ ρ : Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H') ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H')),
      IsDiamondPullbackModL K N H' ρ) :
    IsDiamondPullbackModL K N H' (diamondActionModL K N H') := by
  rw [diamondActionModL, dif_pos h]
  exact h.choose_spec

theorem diamondActionModL_of_not
    (h : ¬ ∃ ρ : Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H') ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H')),
      IsDiamondPullbackModL K N H' ρ) :
    diamondActionModL K N H' = 1 := by
  rw [diamondActionModL, dif_neg h]

variable (K N H')
variable [NeZero N]

def diamondDiffModLH (d : (ZMod N)ˣ) :
    Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] →ₗ[K] Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] :=
  Differential.pullbackAlong (diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)).toAlgHom

theorem diamondDiffModLH_apply (d : (ZMod N)ˣ) (ω : Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) :
    diamondDiffModLH K N H' d ω =
      Differential.pullbackAlong (diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)).toAlgHom ω :=
  rfl

end DiamondDiff

section GenFamily

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

def infSubgroup : Subgroup (ZMod (M / p))ˣ :=
  H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))

omit [Fact p.Prime] [NeZero M] in
theorem mem_infSubgroup_iff (u : (ZMod (M / p))ˣ) :
    u ∈ infSubgroup p M H hpM ↔ ∃ d ∈ H, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d = u :=
  Subgroup.mem_map

omit [Fact p.Prime] [NeZero M] in
theorem unitsMap_mem_infSubgroup {d : (ZMod M)ˣ} (hd : d ∈ H) :
    ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ infSubgroup p M H hpM :=
  Subgroup.mem_map_of_mem _ hd

include hpM in

theorem neZero_div : NeZero (M / p) :=
  ⟨(Nat.div_ne_zero_iff_of_dvd hpM).mpr ⟨NeZero.ne M, (Fact.out : p.Prime).ne_zero⟩⟩

variable (S : Set ℕ)

def genDiffModL : CohCarrier.Gen M S →
    (Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K] →ₗ[K]
      Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K])
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeDiffModLH K (M / p) (infSubgroup p M H hpM) ℓ
  | .U q hq _ =>
      if q = p then
        haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        frobPushDiffModL K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p
      else haveI : NeZero q := ⟨hq.ne_zero⟩; heckeDiffModLH K (M / p) (infSubgroup p M H hpM) q
  | .dia d =>
      haveI : NeZero (M / p) := neZero_div p M hpM
      diamondDiffModLH K (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)

theorem genDiffModL_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) :
    genDiffModL K p M H hpM S (.T ℓ hℓ hℓS hℓM) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeDiffModLH K (M / p) (infSubgroup p M H hpM) ℓ) :=
  rfl

theorem genDiffModL_U_self (hp : p.Prime) (hpM' : p ∣ M) :
    genDiffModL K p M H hpM S (.U p hp hpM') =
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
        frobPushDiffModL K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p) := by
  simp only [genDiffModL, if_true]

theorem genDiffModL_U_of_ne (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p) :
    genDiffModL K p M H hpM S (.U q hq hqM) =
      (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeDiffModLH K (M / p) (infSubgroup p M H hpM) q) := by
  simp only [genDiffModL, if_neg hqp]

theorem genDiffModL_dia (d : (ZMod M)ˣ) :
    genDiffModL K p M H hpM S (.dia d) =
      (haveI : NeZero (M / p) := neZero_div p M hpM;
        diamondDiffModLH K (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)) :=
  rfl

end GenFamily

section TwoComponent

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime] [CharP K p]

def ssNodePairsQExp : Set (Place K (qExpFunctionFieldC K Γ) × Place K (qExpFunctionFieldC K Γ)) :=
  {s | s.2 ∈ ssPlacesQExp K Γ p ∧ s.1 = qExpFrobeniusPlaceModL K Γ p s.2}

variable {K Γ p} in
theorem mem_ssNodePairsQExp_iff (s : Place K (qExpFunctionFieldC K Γ) × Place K (qExpFunctionFieldC K Γ)) :
    s ∈ ssNodePairsQExp K Γ p ↔ s.2 ∈ ssPlacesQExp K Γ p ∧ s.1 = qExpFrobeniusPlaceModL K Γ p s.2 :=
  Iff.rfl

variable {K Γ p} in
theorem frob_mk_mem_ssNodePairsQExp {y : Place K (qExpFunctionFieldC K Γ)} (hy : y ∈ ssPlacesQExp K Γ p) :
    (qExpFrobeniusPlaceModL K Γ p y, y) ∈ ssNodePairsQExp K Γ p :=
  ⟨hy, rfl⟩

def twoCompRegularDifferentials :
    Submodule K (Ω[qExpFunctionFieldC K Γ⁄K] × Ω[qExpFunctionFieldC K Γ⁄K]) :=
  gluedPolarDifferentials K (qExpFunctionFieldC K Γ) (ssNodePairsQExp K Γ p)

end TwoComponent

section PairOperators

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def pairUpModL (C : V →ₗ[K] V) : (V × V) →ₗ[K] (V × V) :=
  LinearMap.prod (C ∘ₗ LinearMap.fst K V V) (-LinearMap.fst K V V)

@[simp]
theorem pairUpModL_apply (C : V →ₗ[K] V) (ω : V × V) : pairUpModL C ω = (C ω.1, -ω.1) :=
  rfl

def pairDiagModL (T : V →ₗ[K] V) : (V × V) →ₗ[K] (V × V) :=
  LinearMap.prodMap T T

@[simp]
theorem pairDiagModL_apply (T : V →ₗ[K] V) (ω : V × V) : pairDiagModL T ω = (T ω.1, T ω.2) :=
  rfl

end PairOperators

section GenPair

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (S : Set ℕ)

def genPairDiffModL (g : CohCarrier.Gen M S) :
    (Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K] ×
        Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K]) →ₗ[K]
      (Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K] ×
        Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K]) :=
  match g with
  | .U q _ _ => if q = p then pairUpModL (genDiffModL K p M H hpM S g) else pairDiagModL (genDiffModL K p M H hpM S g)
  | _ => pairDiagModL (genDiffModL K p M H hpM S g)

end GenPair

end ModularCurve

namespace CuspForm

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ)

theorem natCast_mem_intIdeal : (p : (⊥ : Subring ℂ)) ∈ intIdeal p :=
  Ideal.subset_span rfl

def IntTwoCuspForms : Type :=
  TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)

def IntTwoCuspForms.equivTwoCuspForms :
    IntTwoCuspForms M H p ≃+ TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p) :=
  AddEquiv.refl _

theorem IntTwoCuspForms.nsmul_eq_zero (x : IntTwoCuspForms M H p) : p • x = 0 := by
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

def intTwoCuspReduce : twoCuspLattice M H 2 p (⊥ : Subring ℂ) →+ IntTwoCuspForms M H p :=
  (twoCuspReduce (M := M) (H := H) (k := 2) (p := p) (A := (⊥ : Subring ℂ)) (intIdeal p)).toAddMonoidHom

omit [Fact p.Prime] in
theorem intTwoCuspReduce_apply (x : twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    intTwoCuspReduce M H p x = (twoCuspReduce (intIdeal p) x : TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) :=
  rfl

omit [Fact p.Prime] in
theorem intTwoCuspReduce_surjective : Function.Surjective (intTwoCuspReduce M H p) :=
  twoCuspReduce_surjective M H 2 p (⊥ : Subring ℂ) (intIdeal p)

omit [Fact p.Prime] in

def intTwoCuspGenModAdd (S : Set ℕ) (g : CohCarrier.Gen M S) : IntTwoCuspForms M H p →+ IntTwoCuspForms M H p :=
  (twoCuspGenMod (M := M) (H := H) (k := 2) (p := p) (A := (⊥ : Subring ℂ)) (intIdeal p) S g).toAddMonoidHom

def intTwoCuspGenMod (S : Set ℕ) (g : CohCarrier.Gen M S) :
    IntTwoCuspForms M H p →ₗ[ZMod p] IntTwoCuspForms M H p :=
  (intTwoCuspGenModAdd M H p S g).toZModLinearMap p

theorem intTwoCuspGenMod_apply (S : Set ℕ) (g : CohCarrier.Gen M S) (x : IntTwoCuspForms M H p) :
    intTwoCuspGenMod M H p S g x =
      (twoCuspGenMod (intIdeal p) S g (x : TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) :
        TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) :=
  rfl

theorem intTwoCuspGenMod_reduce (S : Set ℕ) (g : CohCarrier.Gen M S)
    (x : twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    intTwoCuspGenMod M H p S g (intTwoCuspReduce M H p x) =
      intTwoCuspReduce M H p (twoCuspEnd ⟨heckeGenH S 2 g, heckeGenH_mem_heckeRingH S 2 g⟩ x) :=
  rfl

end CuspForm

namespace ModularCurve

open scoped TensorProduct

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  [Algebra (ZMod p) K]

def IsInfReductionMap
    (ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
      Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K]) : Prop :=
  ∀ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ), IsIntegralQExp f pf →
      diffQExp (qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))
          (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
            ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) =
        intSeriesC K pf

variable {K p M H hpM} in
theorem IsInfReductionMap.diffQExp_apply
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
