module
public import Mathlib
public import Def.AlgebraicGeometry_RelativeGroupLaw
public import Def.GoodReductionJacobian_RelativeGroupLawKernel
public import Def.AlgebraicGeometry_RelativePicardFunctor
set_option autoImplicit false


public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

def LocallyIsoOver (q : X ⟶ T) (M M' : X.Modules) : Prop :=
  ∀ τ : T, ∃ U : T.Opens, τ ∈ U ∧
    Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M')

namespace LocallyIsoOver

variable {q : X ⟶ T} {M M' M'' : X.Modules}

def restrict {U V : T.Opens} (hVU : V ≤ U)
    (e : (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M') :
    (Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj M' :=
  have hle : q ⁻¹ᵁ V ≤ q ⁻¹ᵁ U := fun _ hx => hVU hx
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hle) (q ⁻¹ᵁ U).ι).app M).symm ≪≫
      (Scheme.Modules.pullback (X.homOfLE hle)).mapIso e ≪≫
        (Scheme.Modules.pullbackComp (X.homOfLE hle) (q ⁻¹ᵁ U).ι).app M' ≪≫
          (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).app M'

end LocallyIsoOver

end AlgebraicGeometry.Scheme.Modules

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def fstPoint (_L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver (pullback.snd f t ≫ t) f :=
  ⟨pullback.fst f t, pullback.condition⟩

def sndPoint (_L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : SchemeHomOver (pullback.snd f t ≫ t) f :=
  ⟨pullback.snd f t ≫ x.1, by rw [Category.assoc, x.2]⟩

def mulRight (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : pullback f t ⟶ A :=
  (L.mul (pullback.snd f t ≫ t) (L.fstPoint t) (L.sndPoint t x)).1

def translate (L : RelativeGroupLaw R f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : A ⟶ A :=
  (L.mul f idPoint ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩).1

def IsInStabilizer (L : RelativeGroupLaw R f) (𝓛 : A.Modules) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : Prop :=
  Scheme.Modules.LocallyIsoOver (pullback.snd f t)
    ((Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛) ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)

end GoodReductionJacobian.RelativeGroupLaw

end
