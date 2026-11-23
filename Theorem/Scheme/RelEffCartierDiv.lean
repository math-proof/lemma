module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Theorem.Scheme.UniversalDivisor
public import Structure.AlgebraicGeometry_RelEffCartierDiv

public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry


@[ext] public theorem RelEffCartierDiv.ext {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T : Scheme.{u}} {g : T ⟶ S} {D₁ D₂ : RelEffCartierDiv f r g}
    (h : D₁.I = D₂.I) : D₁ = D₂ := by
  cases D₁; cases D₂; cases h; rfl


@[reassoc (attr := simp)]
public theorem mapOnProdOver_fst {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    mapOnProdOver f φ hφ ≫ pullback.fst f g' = pullback.fst f g := by
  simp only [mapOnProdOver, pullback.map, pullback.lift_fst, Category.comp_id]


@[reassoc (attr := simp)]
public theorem mapOnProdOver_snd {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    mapOnProdOver f φ hφ ≫ pullback.snd f g' = pullback.snd f g ≫ φ := by
  simp only [mapOnProdOver, pullback.map, pullback.lift_snd]


@[simp] public theorem mapOnProdOver_id {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S} :
    mapOnProdOver f (𝟙 T) (Category.id_comp g) = 𝟙 (pullback f g) := by
  ext <;> simp


public theorem isPullback_mapOnProdOver {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    IsPullback (mapOnProdOver f φ hφ) (pullback.snd f g) (pullback.snd f g') φ := by
  subst hφ
  refine IsPullback.of_right (h₁₂ := pullback.fst f g') (v₁₃ := f) (h₂₂ := g') ?_
    (mapOnProdOver_snd f φ rfl) (IsPullback.of_hasPullback f g')
  simpa using IsPullback.of_hasPullback f (φ ≫ g')


public theorem isPullback_comapSubschemeMapOver (I : (pullback f g').IdealSheafData) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    IsPullback (comapSubschemeMapOver I φ hφ) (I.comap (mapOnProdOver f φ hφ)).subschemeι
      I.subschemeι (mapOnProdOver f φ hφ) := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso (mapOnProdOver f φ hφ)) ?_ ?_).flip
  · simp [comapSubschemeMapOver]
  · simp
  · simp [comapSubschemeMapOver]


public theorem isPullback_comap_snd_over (I : (pullback f g').IdealSheafData) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    IsPullback (comapSubschemeMapOver I φ hφ)
      ((I.comap (mapOnProdOver f φ hφ)).subschemeι ≫ pullback.snd f g)
      (I.subschemeι ≫ pullback.snd f g') φ :=
  (isPullback_comapSubschemeMapOver I φ hφ).paste_vert (isPullback_mapOnProdOver f φ hφ)

end transport


public theorem pullsBackOver_pullbackAlong {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    PullsBackOver D φ hφ (D.pullbackAlong φ hφ) := rfl


public theorem PullsBackOver.eq_pullbackAlong {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} {D : RelEffCartierDiv f r g'}
    {T : Scheme.{u}} {g : T ⟶ S} {φ : T ⟶ T'} {hφ : φ ≫ g' = g}
    {D' : RelEffCartierDiv f r g} (h : PullsBackOver D φ hφ D') :
    D' = D.pullbackAlong φ hφ :=
  RelEffCartierDiv.ext h.symm


public theorem PullsBackOver.isPullback {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} {D : RelEffCartierDiv f r g'}
    {T : Scheme.{u}} {g : T ⟶ S} {φ : T ⟶ T'} {hφ : φ ≫ g' = g}
    {D' : RelEffCartierDiv f r g} (h : PullsBackOver D φ hφ D') :
    ∃ ψ : D'.I.subscheme ⟶ D.I.subscheme,
      IsPullback ψ (D'.I.subschemeι ≫ pullback.snd f g) (D.I.subschemeι ≫ pullback.snd f g') φ := by
  obtain rfl := h.eq_pullbackAlong
  exact ⟨_, isPullback_comap_snd_over D.I φ hφ⟩


public theorem RelEffCartierDiv.pullbackAlong_comp {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T'' : Scheme.{u}} {g'' : T'' ⟶ S} (D : RelEffCartierDiv f r g'')
    {T' : Scheme.{u}} {g' : T' ⟶ S} (φ : T' ⟶ T'') (hφ : φ ≫ g'' = g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ' : T ⟶ T') (hφ' : φ' ≫ g' = g) :
    (D.pullbackAlong φ hφ).pullbackAlong φ' hφ' =
      D.pullbackAlong (φ' ≫ φ) (by rw [Category.assoc, hφ, hφ']) := by
  refine RelEffCartierDiv.ext ?_
  change (D.I.comap _).comap _ = D.I.comap _
  rw [← Scheme.IdealSheafData.comap_comp]
  congr 1
  ext <;> simp


public theorem RelEffCartierDiv.pullbackAlong_id {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) :
    D.pullbackAlong (𝟙 T) (Category.id_comp g) = D := by
  refine RelEffCartierDiv.ext ?_
  change D.I.comap (mapOnProdOver f (𝟙 T) (Category.id_comp g)) = D.I
  rw [show mapOnProdOver f (𝟙 T) (Category.id_comp g) = 𝟙 _ from mapOnProdOver_id f,
    Scheme.IdealSheafData.comap_id]

section FieldComparison

variable {k : Type u} [Field k]


@[simp] public theorem RelEffCartierDiv.toRelEffDivisor_I {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (D : RelEffCartierDiv c r t) :
    D.toRelEffDivisor.I = D.I := rfl


public theorem RelEffCartierDiv.toRelEffDivisor_injective {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (RelEffCartierDiv.toRelEffDivisor (c := c) (r := r) (t := t)) :=
  fun _ _ h => RelEffCartierDiv.ext (congrArg AlgebraicCurve.RelEffDivisor.I h)


@[simp] public theorem RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (D : AlgebraicCurve.RelEffDivisor C c r T t)
    (h : LocallyOfFinitePresentation (D.I.subschemeι ≫ pullback.snd c t)) :
    (RelEffCartierDiv.ofRelEffDivisor D h).toRelEffDivisor = D := rfl


public theorem RelEffCartierDiv.toRelEffDivisor_pullbackAlong {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (D : RelEffCartierDiv c r t')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ T') (hφ : φ ≫ t' = t) :
    (D.pullbackAlong φ hφ).toRelEffDivisor = D.toRelEffDivisor.pullbackAlong φ hφ := by
  refine AlgebraicCurve.RelEffDivisor.ext ?_
  change D.I.comap (mapOnProdOver c φ hφ) = D.I.comap (AlgebraicCurve.mapOnProd c φ hφ)
  congr 1

end FieldComparison

end AlgebraicGeometry
