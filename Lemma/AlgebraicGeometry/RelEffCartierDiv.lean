import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Lemma.AlgebraicCurve.UniversalDivisor
import Structure.AlgebraicGeometry_RelEffCartierDiv

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry


@[ext] lemma RelEffCartierDiv.ext {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T : Scheme.{u}} {g : T ⟶ S} {D₁ D₂ : RelEffCartierDiv f r g}
    (h : D₁.I = D₂.I) : D₁ = D₂ := by
  cases D₁; cases D₂; cases h; rfl

noncomputable def mapOnProdOver {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    pullback f g ⟶ pullback f g' :=
  pullback.map f g f g' (𝟙 𝒞) φ (𝟙 S) (by simp) (by rw [Category.comp_id, hφ])

@[reassoc (attr := simp)]
lemma mapOnProdOver_fst {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    mapOnProdOver f φ hφ ≫ pullback.fst f g' = pullback.fst f g := by
  simp only [mapOnProdOver, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma mapOnProdOver_snd {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    mapOnProdOver f φ hφ ≫ pullback.snd f g' = pullback.snd f g ≫ φ := by
  simp only [mapOnProdOver, pullback.map, pullback.lift_snd]

@[simp] lemma mapOnProdOver_id {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S} :
    mapOnProdOver f (𝟙 T) (Category.id_comp g) = 𝟙 (pullback f g) := by
  ext <;> simp

lemma isPullback_mapOnProdOver {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    IsPullback (mapOnProdOver f φ hφ) (pullback.snd f g) (pullback.snd f g') φ := by
  subst hφ
  refine IsPullback.of_right (h₁₂ := pullback.fst f g') (v₁₃ := f) (h₂₂ := g') ?_
    (mapOnProdOver_snd f φ rfl) (IsPullback.of_hasPullback f g')
  simpa using IsPullback.of_hasPullback f (φ ≫ g')

def PullsBackOver {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g)
    (D' : RelEffCartierDiv f r g) : Prop :=
  D.I.comap (mapOnProdOver f φ hφ) = D'.I

section transport

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}

noncomputable def comapSubschemeMapOver (I : (pullback f g').IdealSheafData) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) : (I.comap (mapOnProdOver f φ hφ)).subscheme ⟶ I.subscheme :=
  (I.comapIso (mapOnProdOver f φ hφ)).hom ≫ pullback.snd _ _

lemma isPullback_comapSubschemeMapOver (I : (pullback f g').IdealSheafData) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    IsPullback (comapSubschemeMapOver I φ hφ) (I.comap (mapOnProdOver f φ hφ)).subschemeι
      I.subschemeι (mapOnProdOver f φ hφ) := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso (mapOnProdOver f φ hφ)) ?_ ?_).flip
  · simp [comapSubschemeMapOver]
  · simp
  · simp [comapSubschemeMapOver]

lemma isPullback_comap_snd_over (I : (pullback f g').IdealSheafData) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    IsPullback (comapSubschemeMapOver I φ hφ)
      ((I.comap (mapOnProdOver f φ hφ)).subschemeι ≫ pullback.snd f g)
      (I.subschemeι ≫ pullback.snd f g') φ :=
  (isPullback_comapSubschemeMapOver I φ hφ).paste_vert (isPullback_mapOnProdOver f φ hφ)

end transport

noncomputable def RelEffCartierDiv.pullbackAlong {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) : RelEffCartierDiv f r g where
  I := D.I.comap (mapOnProdOver f φ hφ)
  isFinite :=
    have := D.isFinite
    MorphismProperty.of_isPullback (isPullback_comap_snd_over D.I φ hφ) ‹_›
  flat :=
    have := D.flat
    MorphismProperty.of_isPullback (isPullback_comap_snd_over D.I φ hφ) ‹_›
  locallyOfFinitePresentation :=
    have := D.locallyOfFinitePresentation
    MorphismProperty.of_isPullback (isPullback_comap_snd_over D.I φ hφ) ‹_›
  finrank_eq t := by
    have := D.isFinite
    have := D.flat
    have := D.locallyOfFinitePresentation
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_comap_snd_over D.I φ hφ) t]
    exact D.finrank_eq (φ t)

theorem pullsBackOver_pullbackAlong {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    PullsBackOver D φ hφ (D.pullbackAlong φ hφ) := rfl

lemma PullsBackOver.eq_pullbackAlong {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} {D : RelEffCartierDiv f r g'}
    {T : Scheme.{u}} {g : T ⟶ S} {φ : T ⟶ T'} {hφ : φ ≫ g' = g}
    {D' : RelEffCartierDiv f r g} (h : PullsBackOver D φ hφ D') :
    D' = D.pullbackAlong φ hφ :=
  RelEffCartierDiv.ext h.symm

lemma PullsBackOver.isPullback {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} {D : RelEffCartierDiv f r g'}
    {T : Scheme.{u}} {g : T ⟶ S} {φ : T ⟶ T'} {hφ : φ ≫ g' = g}
    {D' : RelEffCartierDiv f r g} (h : PullsBackOver D φ hφ D') :
    ∃ ψ : D'.I.subscheme ⟶ D.I.subscheme,
      IsPullback ψ (D'.I.subschemeι ≫ pullback.snd f g) (D.I.subschemeι ≫ pullback.snd f g') φ := by
  obtain rfl := h.eq_pullbackAlong
  exact ⟨_, isPullback_comap_snd_over D.I φ hφ⟩

lemma RelEffCartierDiv.pullbackAlong_comp {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
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

lemma RelEffCartierDiv.pullbackAlong_id {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) :
    D.pullbackAlong (𝟙 T) (Category.id_comp g) = D := by
  refine RelEffCartierDiv.ext ?_
  change D.I.comap (mapOnProdOver f (𝟙 T) (Category.id_comp g)) = D.I
  rw [show mapOnProdOver f (𝟙 T) (Category.id_comp g) = 𝟙 _ from mapOnProdOver_id f,
    Scheme.IdealSheafData.comap_id]

section FieldComparison

variable {k : Type u} [Field k]

def RelEffCartierDiv.toRelEffDivisor {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (D : RelEffCartierDiv c r t) :
    AlgebraicCurve.RelEffDivisor C c r T t :=
  ⟨D.I, D.isFinite, D.flat, D.finrank_eq⟩

@[simp] lemma RelEffCartierDiv.toRelEffDivisor_I {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (D : RelEffCartierDiv c r t) :
    D.toRelEffDivisor.I = D.I := rfl

lemma RelEffCartierDiv.toRelEffDivisor_injective {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (RelEffCartierDiv.toRelEffDivisor (c := c) (r := r) (t := t)) :=
  fun _ _ h => RelEffCartierDiv.ext (congrArg AlgebraicCurve.RelEffDivisor.I h)

def RelEffCartierDiv.ofRelEffDivisor {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (D : AlgebraicCurve.RelEffDivisor C c r T t)
    (h : LocallyOfFinitePresentation (D.I.subschemeι ≫ pullback.snd c t)) :
    RelEffCartierDiv c r t :=
  ⟨D.I, D.isFinite, D.flat, h, D.finrank_eq⟩

@[simp] lemma RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (D : AlgebraicCurve.RelEffDivisor C c r T t)
    (h : LocallyOfFinitePresentation (D.I.subschemeι ≫ pullback.snd c t)) :
    (RelEffCartierDiv.ofRelEffDivisor D h).toRelEffDivisor = D := rfl

lemma RelEffCartierDiv.toRelEffDivisor_pullbackAlong {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (D : RelEffCartierDiv c r t')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ T') (hφ : φ ≫ t' = t) :
    (D.pullbackAlong φ hφ).toRelEffDivisor = D.toRelEffDivisor.pullbackAlong φ hφ := by
  refine AlgebraicCurve.RelEffDivisor.ext ?_
  change D.I.comap (mapOnProdOver c φ hφ) = D.I.comap (AlgebraicCurve.mapOnProd c φ hφ)
  congr 1

end FieldComparison

end AlgebraicGeometry
