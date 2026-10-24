import Lemma.Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Lemma.Definitions.Def_EllipticCurve_TateModule

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RiemannForm

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

theorem specMap_algebraMap_self :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) :=
  Spec.map_id _

abbrev Pt : Type := SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k))) f

def toUnitPt (x : Pt f) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
  ⟨x.1, by rw [x.2, specMap_algebraMap_self]⟩

def ofUnitPt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : Pt f :=
  ⟨x.1, by rw [x.2, specMap_algebraMap_self]⟩

@[simp] theorem toUnitPt_coe (x : Pt f) : (toUnitPt f x).1 = x.1 := rfl
@[simp] theorem ofUnitPt_coe (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : (ofUnitPt f x).1 = x.1 := rfl
@[simp] theorem ofUnitPt_toUnitPt (x : Pt f) : ofUnitPt f (toUnitPt f x) = x := Subtype.ext rfl
@[simp] theorem toUnitPt_ofUnitPt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    toUnitPt f (ofUnitPt f x) = x := Subtype.ext rfl

def constPt (x : Pt f) : SchemeHomOver f f :=
  ⟨f ≫ x.1, by rw [Category.assoc, x.2, specMap_algebraMap_self, Category.comp_id]⟩

variable (L : RelativeGroupLaw k f)

def translation (x : Pt f) : A ⟶ A :=
  (L.mul f RelativeGroupLaw.idPoint (constPt f x)).1

theorem translation_over (x : Pt f) : translation f L x ≫ f = f :=
  (L.mul f RelativeGroupLaw.idPoint (constPt f x)).2

def transportIso {T g : A ⟶ A} (h : T ≫ g = g) (M : A.Modules) :
    (Scheme.Modules.pullback T).obj ((Scheme.Modules.pullback g).obj M) ≅ (Scheme.Modules.pullback g).obj M :=
  (Scheme.Modules.pullbackComp T g).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

def IsConstScalar {M : A.Modules} (σ : M ⟶ M) (c : k) : Prop :=
  ∀ (U : A.Opens) (s : Γ(M, U)),
    σ.app U s = (A.presheaf.map (homOfLE (le_top (a := U))).op (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) • s

def IsLevelPairingValue (𝓛 : A.Modules) (n : ℕ) (x y : Pt f) (c : k) : Prop :=
  ∃ (hx : translation f L x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (β : (Scheme.Modules.pullback (L.schemeNsmul n)).obj ((Scheme.Modules.pullback (translation f L y)).obj 𝓛) ≅
      (Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛),
    IsConstScalar f
      (β.symm ≪≫ (transportIso hx ((Scheme.Modules.pullback (translation f L y)).obj 𝓛)).symm ≪≫
        (Scheme.Modules.pullback (translation f L x)).mapIso β ≪≫ transportIso hx 𝓛).hom c

variable (hc : L.IsCommutative)

def IsRiemannForm (𝓛 : A.Modules) (ℓ : ℕ) [Fact ℓ.Prime] (ζ : ℕ → k)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) : Prop :=
  ∀ (n : ℕ) (a b : TateModule ℓ (L.AlgPoints hc k)),
    IsLevelPairingValue f L 𝓛 (ℓ ^ n)
      (RelativeGroupLaw.AlgPoints.toPoint ((a : ℕ → L.AlgPoints hc k) n))
      (RelativeGroupLaw.AlgPoints.toPoint ((b : ℕ → L.AlgPoints hc k) n))
      (ζ n ^ (e a b).appr n)

end AlgebraicGeometry.RiemannForm

end
