import Mathlib
import Lemma.AlgebraicGeometry.RelativeGroupLaw
import Lemma.GoodReductionJacobian.RelativeGroupLawKernel
import Def.AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

def LocallyIsoOver (q : X ⟶ T) (M M' : X.Modules) : Prop :=
  ∀ τ : T, ∃ U : T.Opens, τ ∈ U ∧
    Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M')

namespace LocallyIsoOver

variable {q : X ⟶ T} {M M' M'' : X.Modules}

theorem of_iso (q : X ⟶ T) {M M' : X.Modules} (e : M ≅ M') : LocallyIsoOver q M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem rfl : LocallyIsoOver q M M := of_iso q (Iso.refl M)

theorem symm (h : LocallyIsoOver q M M') : LocallyIsoOver q M' M := fun τ => by
  obtain ⟨U, hτ, ⟨e⟩⟩ := h τ
  exact ⟨U, hτ, ⟨e.symm⟩⟩

def restrict {U V : T.Opens} (hVU : V ≤ U)
    (e : (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M') :
    (Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj M' :=
  have hle : q ⁻¹ᵁ V ≤ q ⁻¹ᵁ U := fun _ hx => hVU hx
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hle) (q ⁻¹ᵁ U).ι).app M).symm ≪≫
      (Scheme.Modules.pullback (X.homOfLE hle)).mapIso e ≪≫
        (Scheme.Modules.pullbackComp (X.homOfLE hle) (q ⁻¹ᵁ U).ι).app M' ≪≫
          (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).app M'

theorem trans (h : LocallyIsoOver q M M') (h' : LocallyIsoOver q M' M'') : LocallyIsoOver q M M'' := fun τ => by
  obtain ⟨U, hτ, ⟨e⟩⟩ := h τ
  obtain ⟨U', hτ', ⟨e'⟩⟩ := h' τ
  exact ⟨U ⊓ U', ⟨hτ, hτ'⟩, ⟨restrict inf_le_left e ≪≫ restrict inf_le_right e'⟩⟩

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

@[simp] theorem fstPoint_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.fstPoint t).1 = pullback.fst f t := rfl

@[simp] theorem sndPoint_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : (L.sndPoint t x).1 = pullback.snd f t ≫ x.1 := rfl

def mulRight (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : pullback f t ⟶ A :=
  (L.mul (pullback.snd f t ≫ t) (L.fstPoint t) (L.sndPoint t x)).1

theorem mulRight_over (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : L.mulRight t x ≫ f = pullback.snd f t ≫ t :=
  (L.mul (pullback.snd f t ≫ t) (L.fstPoint t) (L.sndPoint t x)).2

theorem sndPoint_one (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    L.sndPoint t (L.one t) = L.one (pullback.snd f t ≫ t) := by
  have h := L.one_natural t (pullback.snd f t ≫ t) (pullback.snd f t) rfl
  rw [← h]
  rfl

theorem mulRight_one (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    L.mulRight t (L.one t) = pullback.fst f t := by
  unfold mulRight
  rw [sndPoint_one, L.mul_one]
  rfl

def translate (L : RelativeGroupLaw R f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : A ⟶ A :=
  (L.mul f idPoint ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩).1

theorem translate_over (L : RelativeGroupLaw R f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.translate x ≫ f = f :=
  (L.mul f idPoint ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩).2

theorem translate_one (L : RelativeGroupLaw R f) : L.translate (L.one (𝟙 (Spec (CommRingCat.of R)))) = 𝟙 A := by
  have h : (⟨f ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1, by
      rw [Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id]⟩ : SchemeHomOver f f) =
      L.one f := by
    have h1 := L.one_natural (𝟙 (Spec (CommRingCat.of R))) f f (Category.comp_id f)
    rw [← h1]
    rfl
  unfold translate
  rw [h, L.mul_one]

def IsInStabilizer (L : RelativeGroupLaw R f) (𝓛 : A.Modules) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : Prop :=
  Scheme.Modules.LocallyIsoOver (pullback.snd f t)
    ((Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛) ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)

theorem isInStabilizer_one (L : RelativeGroupLaw R f) (𝓛 : A.Modules) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : L.IsInStabilizer 𝓛 t (L.one t) := by
  unfold IsInStabilizer
  rw [mulRight_one]
  exact Scheme.Modules.LocallyIsoOver.rfl

theorem isInStabilizer_unit (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : L.IsInStabilizer (SheafOfModules.unit A.ringCatSheaf) t x := by
  exact Scheme.Modules.LocallyIsoOver.of_iso _
    (Scheme.Modules.pullbackUnitIso (L.mulRight t x) ≪≫ (Scheme.Modules.pullbackUnitIso (pullback.fst f t)).symm)

end GoodReductionJacobian.RelativeGroupLaw

end
