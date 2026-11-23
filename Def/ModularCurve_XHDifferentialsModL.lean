import Mathlib
import Lemma.UpperHalfPlane.XHDiamondModL
import Def.ModularCurve_QExpFrobeniusModL
import Def.ModularCurve_HeckeDifferential
import Def.AlgebraicCurve_PolarDifferentials
import Lemma.WeierstrassCurve.SupersingularModuli
import Def.CuspForm_TwoCuspLattice
import Abbrev.ModularCurve_XHDifferentialsModL

set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve IntermediateField CongruenceSubgroup Set

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
def ssPolarDifferentials : Submodule K Ω[qExpFunctionFieldC K Γ⁄K] :=
  polarDifferentials K (qExpFunctionFieldC K Γ) (ssPlacesQExp K Γ p)

end Supersingular

section Decimate

variable (K : Type*) [Field K] (p : ℕ) [NeZero p]

variable {K p} in
def qDecimate : LaurentSeries K →ₗ[K] LaurentSeries K where
  toFun x := HahnSeries.ofSuppBddBelow (fun k : ℤ => x.coeff ((p : ℤ) * k)) (bddBelow_support_decimate x)
  map_add' x y := by
    ext k
    simp only [HahnSeries.coeff_ofSuppBddBelow, HahnSeries.coeff_add]
  map_smul' c x := by
    ext k
    simp only [HahnSeries.coeff_ofSuppBddBelow, HahnSeries.coeff_smul, RingHom.id_apply]

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

end FrobPush

section HeckeDiff

variable (K : Type*) [Field K] (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]

def heckeAlphaModLH :
    qExpFunctionFieldC K (CohCarrier.GammaH N H') →ₐ[K]
      qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) :=
  IntermediateField.inclusion (qExpFunctionFieldC_mono K inf_le_left)

omit [NeZero ℓ] in
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

open Classical in

def heckeBetaModLH :
    qExpFunctionFieldC K (CohCarrier.GammaH N H') →ₐ[K]
      qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) :=
  if h : HeckeBetaModLHDefined K N H' ℓ then heckeBetaModLHOf K N H' ℓ h else heckeAlphaModLH K N H' ℓ

def heckeDiffModLH :
    Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] →ₗ[K] Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] :=
  Differential.correspondence (heckeBetaModLH K N H' ℓ) (heckeAlphaModLH K N H' ℓ)

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

variable (K N H')
variable [NeZero N]

def diamondDiffModLH (d : (ZMod N)ˣ) :
    Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] →ₗ[K] Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] :=
  Differential.pullbackAlong (diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)).toAlgHom

end DiamondDiff

section GenFamily

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

def infSubgroup : Subgroup (ZMod (M / p))ˣ :=
  H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))

omit [Fact p.Prime] [NeZero M] in
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

end GenFamily

section TwoComponent

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime] [CharP K p]

def ssNodePairsQExp : Set (Place K (qExpFunctionFieldC K Γ) × Place K (qExpFunctionFieldC K Γ)) :=
  {s | s.2 ∈ ssPlacesQExp K Γ p ∧ s.1 = qExpFrobeniusPlaceModL K Γ p s.2}

variable {K Γ p} in
variable {K Γ p} in
def twoCompRegularDifferentials :
    Submodule K (Ω[qExpFunctionFieldC K Γ⁄K] × Ω[qExpFunctionFieldC K Γ⁄K]) :=
  gluedPolarDifferentials K (qExpFunctionFieldC K Γ) (ssNodePairsQExp K Γ p)

end TwoComponent

section PairOperators

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def pairUpModL (C : V →ₗ[K] V) : (V × V) →ₗ[K] (V × V) :=
  LinearMap.prod (C ∘ₗ LinearMap.fst K V V) (-LinearMap.fst K V V)

def pairDiagModL (T : V →ₗ[K] V) : (V × V) →ₗ[K] (V × V) :=
  LinearMap.prodMap T T

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

def IntTwoCuspForms : Type :=
  TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)

def IntTwoCuspForms.equivTwoCuspForms :
    IntTwoCuspForms M H p ≃+ TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p) :=
  AddEquiv.refl _

variable [Fact p.Prime]

omit [Fact p.Prime] in

def intTwoCuspReduce : twoCuspLattice M H 2 p (⊥ : Subring ℂ) →+ IntTwoCuspForms M H p :=
  (twoCuspReduce (M := M) (H := H) (k := 2) (p := p) (A := (⊥ : Subring ℂ)) (intIdeal p)).toAddMonoidHom

omit [Fact p.Prime] in
def intTwoCuspGenModAdd (S : Set ℕ) (g : CohCarrier.Gen M S) : IntTwoCuspForms M H p →+ IntTwoCuspForms M H p :=
  (twoCuspGenMod (M := M) (H := H) (k := 2) (p := p) (A := (⊥ : Subring ℂ)) (intIdeal p) S g).toAddMonoidHom

def intTwoCuspGenMod (S : Set ℕ) (g : CohCarrier.Gen M S) :
    IntTwoCuspForms M H p →ₗ[ZMod p] IntTwoCuspForms M H p :=
  (intTwoCuspGenModAdd M H p S g).toZModLinearMap p

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

end ModularCurve

end
