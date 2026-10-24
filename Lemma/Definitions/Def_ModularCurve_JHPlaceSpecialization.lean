import Mathlib
import Lemma.Definitions.Def_ModularCurve_JHNeronObjectAtP
import Lemma.Definitions.Def_AlgebraicCurve_RegularProlongation

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups
set_option quotPrecheck false

namespace ModularCurve

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
variable (A : ValuationSubring (AlgebraicClosure ℚ))

namespace JHPlaceSpecialization

def inertiaInvariants : AddSubgroup (JH M H) where
  carrier := {x | ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x}
  zero_mem' := fun σ _ => smul_zero σ
  add_mem' := by
    intro x y hx hy σ hσ
    rw [smul_add, hx σ hσ, hy σ hσ]
  neg_mem' := by
    intro x hx σ hσ
    rw [smul_neg, hx σ hσ]

def PrimeToTorsion (x : JH M H) : Prop := ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ m • x = 0

end JHPlaceSpecialization

variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

local notation "κ" => ResidueField ↥A
local notation "FM" => ↥(xHFunctionFieldBar M H)
local notation "FMp" => ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)
local notation "Γ′" => ModularCurve.JHNeronObjectAtP.ΓN p M H hpM

namespace JHPlaceSpecialization

def IsAffinePlace (v : Place κ Fb) : Prop :=
  ∃ (x : Fb) (a : κ), ((x : Fb) : LaurentSeries κ) = jqModC κ ∧ v.HasValue x a

def Fixed (δ : Place κ Fb → Place κ Fb) (v : Place κ Fb) : Prop :=
  qExpFrobeniusPlaceModL κ Γ′ p (δ (qExpFrobeniusPlaceModL κ Γ′ p v)) = v

end JHPlaceSpecialization

structure JHPlaceSpecialization where

  sp : Place (AlgebraicClosure ℚ) FMp → Place κ Fb

  spPic0 : Pic0 (AlgebraicClosure ℚ) FMp →+ Pic0 κ Fb

  d0_qexp : ∀ (f : FMp) (y : LaurentSeries ↥A),
    coeffMap A.subtype y = ((f : FMp) : LaurentSeries (AlgebraicClosure ℚ)) →
    ∀ g : Fb, ((g : Fb) : LaurentSeries κ) = coeffMap (IsLocalRing.residue ↥A) y → g ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FMp, (∀ v, D v = v.ord f) →
      ∀ v' : Place κ Fb, Finsupp.mapDomain sp D v' = v'.ord g

  d4 : Function.Surjective sp

  d5 : ∀ f : FMp, f ≠ 0 → ∀ D : Divisor (AlgebraicClosure ℚ) FMp, (∀ v, D v = v.ord f) →
    ∃ g : Fb, g ≠ 0 ∧ ∀ v' : Place κ Fb, Finsupp.mapDomain sp D v' = v'.ord g

  d6_inertia : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
    ∀ w : Place (AlgebraicClosure ℚ) FMp,
      sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) = sp w

  d6_frobenius : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
    ∀ w : Place (AlgebraicClosure ℚ) FMp,
      sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) =
        qExpFrobeniusPlaceModL κ Γ′ p (sp w)

  spPic0_compat : ∀ D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := FMp),
    ∃ D' : Divisor.degZero (K := κ) (F := Fb),
      (D' : Divisor κ Fb) = Finsupp.mapDomain sp (D : Divisor (AlgebraicClosure ℚ) FMp) ∧ spPic0 (Pic0.mk D) = Pic0.mk D'

namespace JHPlaceSpecialization

variable {p M H hpM A}

def reduceFst (P : JHPlaceSpecialization p M H hpM A) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (W : Place (AlgebraicClosure ℚ) FM) : Place κ Fb :=
  P.sp (W.restrictAlong α hα)

def reduceSnd (P : JHPlaceSpecialization p M H hpM A) (β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (W : Place (AlgebraicClosure ℚ) FM) : Place κ Fb :=
  δ (P.sp (W.restrictAlong β hβ))

def IsStrictFst (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  δ (qExpFrobeniusPlaceModL κ Γ′ p (P.reduceFst α hα W)) = P.reduceSnd β hβ δ W ∧ ¬ Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (P.reduceFst α hα W)

def IsStrictSnd (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  P.reduceFst α hα W = qExpFrobeniusPlaceModL κ Γ′ p (P.reduceSnd β hβ δ W) ∧ ¬ Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (P.reduceSnd β hβ δ W)

def TypeDichotomy (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  ∀ W : Place (AlgebraicClosure ℚ) FM,
    P.reduceFst α hα W = qExpFrobeniusPlaceModL κ Γ′ p (P.reduceSnd β hβ δ W) ∨
      δ (qExpFrobeniusPlaceModL κ Γ′ p (P.reduceFst α hα W)) = P.reduceSnd β hβ δ W

def IsGoodDiv (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (D : Divisor (AlgebraicClosure ℚ) FM) : Prop :=
  ∀ W ∈ D.support, P.IsStrictFst α β hα hβ δ W ∨ P.IsStrictSnd α β hα hβ δ W

open Classical in

def fstDiv (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (D : Divisor (AlgebraicClosure ℚ) FM) : Divisor (AlgebraicClosure ℚ) FM :=
  D.filter (P.IsStrictFst α β hα hβ δ)

open Classical in

def sndDiv (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (D : Divisor (AlgebraicClosure ℚ) FM) : Divisor (AlgebraicClosure ℚ) FM :=
  D.filter (P.IsStrictSnd α β hα hβ δ)

def glueData (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb)) (D : Divisor (AlgebraicClosure ℚ) FM) : GluingData κ Fb SS :=
  (Finsupp.mapDomain (P.reduceFst α hα) (P.fstDiv α β hα hβ δ D),
    Finsupp.mapDomain (P.reduceSnd β hβ δ) (P.sndDiv α β hα hβ δ D), 0)

def IsGluedSpecialization (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral)
    (hβ : β.IsIntegral) (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb))
    (spJ : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ GluedPic0 κ Fb SS) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM)))
    (hI : Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A) (x : ↥(GluingData.admissible SS)),
    P.IsGoodDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) FM) →
    (x : GluingData κ Fb SS) = P.glueData α β hα hβ δ SS D →
      spJ ⟨Pic0.mk D, hI⟩ = GluedPic0.mk SS x

def IsGoodClass (P : JHPlaceSpecialization p M H hpM A) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb)) (x : JH M H) : Prop :=
  ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM)),
    P.IsGoodDiv α β hα hβ δ (D : Divisor (AlgebraicClosure ℚ) FM) ∧ P.glueData α β hα hβ δ SS D ∈ GluingData.admissible SS ∧ Pic0.mk D = x

def IsCuspidal (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  ∀ (x : FM), ((x : FM) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
    ∀ a : ↥A, W.ord (x - algebraMap (AlgebraicClosure ℚ) FM (a : AlgebraicClosure ℚ)) ≤ 0

def IsCuspidal' (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ∀ (x : FM), ((x : FM) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) →
    ∀ a : ↥A, W.ord (x - algebraMap (AlgebraicClosure ℚ) FM (a : AlgebraicClosure ℚ)) ≤ 0

def IsInftySide (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  IsCuspidal (M := M) (H := H) (A := A) W ∧
    ∃ (x x' : FM), ((x : FM) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) ∧
      ((x' : FM) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) ∧
      ∃ τ : ↥A, IsLocalRing.residue ↥A τ = 1 ∧ W.HasValue (x' / x ^ p) (τ : AlgebraicClosure ℚ)

def IsZeroSide (W : Place (AlgebraicClosure ℚ) FM) : Prop :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  IsCuspidal' (p := p) (M := M) (H := H) (A := A) W ∧
    ∃ (x x' : FM), ((x : FM) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) ∧
      ((x' : FM) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) ∧
      ∃ τ : ↥A, IsLocalRing.residue ↥A τ = 1 ∧ W.HasValue (x / x' ^ p) (τ : AlgebraicClosure ℚ)

structure ProlongationDatum (P : JHPlaceSpecialization p M H hpM A) (θ : FM ≃ₐ[AlgebraicClosure ℚ] FM) where

  R₁ : RegularProlongation A FM Fb

  R₂ : RegularProlongation A FM Fb

  residue₁_coeffMap : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
    ∃ h : (⟨coeffMap A.subtype y, hy⟩ : FM) ∈ R₁.integers,
      ((R₁.residue ⟨_, h⟩ : Fb) : LaurentSeries κ) = coeffMap (IsLocalRing.residue ↥A) y

  mem_integers₂_iff : ∀ f : FM, f ∈ R₂.integers ↔ θ f ∈ R₁.integers
  residue₂_eq : ∀ (f : FM) (h : f ∈ R₂.integers), R₂.residue ⟨f, h⟩ = R₁.residue ⟨θ f, (mem_integers₂_iff f).mp h⟩

namespace ProlongationDatum

variable {P : JHPlaceSpecialization p M H hpM A}
variable {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}

def DivisorLawFst (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
      ∀ v : Place κ Fb, ¬ Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
        Finsupp.mapDomain (P.reduceFst α hα) (P.fstDiv α β hα hβ δ D) v = v.ord (R.R₁.residue ⟨f, h₁⟩)

def DivisorLawSnd (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
      ∀ v : Place κ Fb, ¬ Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
        Finsupp.mapDomain (P.reduceSnd β hβ δ) (P.sndDiv α β hα hβ δ D) v = v.ord (R.R₂.residue ⟨f, h₂⟩)

open Classical in

def CuspLawInfty (R : ProlongationDatum P θ) (α : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
      ∀ c : Place (AlgebraicClosure ℚ) FM, IsInftySide (p := p) (M := M) (H := H) (A := A) c →
        Finsupp.mapDomain (P.reduceFst α hα) (D.filter (IsInftySide (p := p) (M := M) (H := H) (A := A))) (P.reduceFst α hα c) =
          (P.reduceFst α hα c).ord (R.R₁.residue ⟨f, h₁⟩)

open Classical in

def CuspLawZero (R : ProlongationDatum P θ) (β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
      ∀ c : Place (AlgebraicClosure ℚ) FM, IsZeroSide (p := p) (M := M) (H := H) (A := A) c →
        Finsupp.mapDomain (P.reduceSnd β hβ δ) (D.filter (IsZeroSide (p := p) (M := M) (H := H) (A := A))) (P.reduceSnd β hβ δ c) =
          (P.reduceSnd β hβ δ c).ord (R.R₂.residue ⟨f, h₂⟩)

def OrderLawFixed (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
      ∀ v : Place κ Fb, Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v →
        Finsupp.mapDomain (P.reduceFst α hα) D v =
          v.ord (R.R₁.residue ⟨f, h₁⟩) + (δ (qExpFrobeniusPlaceModL κ Γ′ p v)).ord (R.R₂.residue ⟨f, h₂⟩)

def NodeValueLaw (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb)) : Prop :=
  ∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    ∀ s ∈ SS,
      (∀ V : Place (AlgebraicClosure ℚ) FM, V.ord f ≠ 0 → ¬ (P.reduceFst α hα V = s.1 ∧ P.reduceSnd β hβ δ V = s.2)) →
      ∃ c : κ, c ≠ 0 ∧ s.1.HasValue (R.R₁.residue ⟨f, h₁⟩ : Fb) c ∧ s.2.HasValue (R.R₂.residue ⟨f, h₂⟩ : Fb) c

def RegularityLaw (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) (SS : Finset (Place κ Fb × Place κ Fb)) : Prop :=
  (∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers) (v : Place κ Fb),
      Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v →
      (∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = v → 0 ≤ V.ord f) →
      (R.R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.R₁.residue ⟨f, h₁⟩)) ∧
      (R.R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ (δ (qExpFrobeniusPlaceModL κ Γ′ p v)).ord (R.R₂.residue ⟨f, h₂⟩))) ∧
  (∀ (f : FM) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers), ∀ s ∈ SS,
      (∀ V : Place (AlgebraicClosure ℚ) FM, P.reduceFst α hα V = s.1 → 0 ≤ V.ord f) →
      ∃ c : κ, s.1.HasValue (R.R₁.residue ⟨f, h₁⟩ : Fb) c ∧ s.2.HasValue (R.R₂.residue ⟨f, h₂⟩ : Fb) c)

def IsModel (R : ProlongationDatum P θ) (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place κ Fb → Place κ Fb) : Prop :=
  R.DivisorLawFst α β hα hβ δ ∧ R.DivisorLawSnd α β hα hβ δ ∧ R.CuspLawInfty α hα ∧ R.CuspLawZero β hβ δ

end ProlongationDatum
end JHPlaceSpecialization

end ModularCurve

end
