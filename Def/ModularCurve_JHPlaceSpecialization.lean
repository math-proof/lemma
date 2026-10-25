import Mathlib
import Def.ModularCurve_JHNeronObjectAtP
import Lemma.AlgebraicCurve.RegularProlongation
import Structure.ModularCurve_JHPlaceSpecialization
import Notation.ModularCurve_JHPlaceSpecialization

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

open scoped ModularCurve_JHPlaceSpecialization

namespace JHPlaceSpecialization

def IsAffinePlace (v : Place κ Fb) : Prop :=
  ∃ (x : Fb) (a : κ), ((x : Fb) : LaurentSeries κ) = jqModC κ ∧ v.HasValue x a

def Fixed (δ : Place κ Fb → Place κ Fb) (v : Place κ Fb) : Prop :=
  qExpFrobeniusPlaceModL κ Γ′ p (δ (qExpFrobeniusPlaceModL κ Γ′ p v)) = v

end JHPlaceSpecialization


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
