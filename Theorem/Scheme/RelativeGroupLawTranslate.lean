module

public import Mathlib
public import Theorem.Scheme.RelativeGroupLaw
public import Theorem.Scheme.RelativeGroupLawKernel
public import Def.AlgebraicGeometry_RelativePicardFunctor

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}


public theorem of_iso (q : X ⟶ T) {M M' : X.Modules} (e : M ≅ M') : LocallyIsoOver q M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩


public theorem rfl : LocallyIsoOver q M M := of_iso q (Iso.refl M)


public theorem symm (h : LocallyIsoOver q M M') : LocallyIsoOver q M' M := fun τ => by
  obtain ⟨U, hτ, ⟨e⟩⟩ := h τ
  exact ⟨U, hτ, ⟨e.symm⟩⟩


public theorem trans (h : LocallyIsoOver q M M') (h' : LocallyIsoOver q M' M'') : LocallyIsoOver q M M'' := fun τ => by
  obtain ⟨U, hτ, ⟨e⟩⟩ := h τ
  obtain ⟨U', hτ', ⟨e'⟩⟩ := h' τ
  exact ⟨U ⊓ U', ⟨hτ, hτ'⟩, ⟨restrict inf_le_left e ≪≫ restrict inf_le_right e'⟩⟩

end LocallyIsoOver

end AlgebraicGeometry.Scheme.Modules

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}


@[simp] public theorem fstPoint_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.fstPoint t).1 = pullback.fst f t := rfl


@[simp] public theorem sndPoint_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : (L.sndPoint t x).1 = pullback.snd f t ≫ x.1 := rfl


public theorem mulRight_over (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : L.mulRight t x ≫ f = pullback.snd f t ≫ t :=
  (L.mul (pullback.snd f t ≫ t) (L.fstPoint t) (L.sndPoint t x)).2


public theorem sndPoint_one (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    L.sndPoint t (L.one t) = L.one (pullback.snd f t ≫ t) := by
  have h := L.one_natural t (pullback.snd f t ≫ t) (pullback.snd f t) rfl
  rw [← h]
  rfl


public theorem mulRight_one (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    L.mulRight t (L.one t) = pullback.fst f t := by
  unfold mulRight
  rw [sndPoint_one, L.mul_one]
  rfl


public theorem translate_over (L : RelativeGroupLaw R f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.translate x ≫ f = f :=
  (L.mul f idPoint ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩).2


public theorem translate_one (L : RelativeGroupLaw R f) : L.translate (L.one (𝟙 (Spec (CommRingCat.of R)))) = 𝟙 A := by
  have h : (⟨f ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1, by
      rw [Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id]⟩ : SchemeHomOver f f) =
      L.one f := by
    have h1 := L.one_natural (𝟙 (Spec (CommRingCat.of R))) f f (Category.comp_id f)
    rw [← h1]
    rfl
  unfold translate
  rw [h, L.mul_one]


public theorem isInStabilizer_one (L : RelativeGroupLaw R f) (𝓛 : A.Modules) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : L.IsInStabilizer 𝓛 t (L.one t) := by
  unfold IsInStabilizer
  rw [mulRight_one]
  exact Scheme.Modules.LocallyIsoOver.rfl


public theorem isInStabilizer_unit (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : L.IsInStabilizer (SheafOfModules.unit A.ringCatSheaf) t x := by
  exact Scheme.Modules.LocallyIsoOver.of_iso _
    (Scheme.Modules.pullbackUnitIso (L.mulRight t x) ≪≫ (Scheme.Modules.pullbackUnitIso (pullback.fst f t)).symm)

end GoodReductionJacobian.RelativeGroupLaw

end
