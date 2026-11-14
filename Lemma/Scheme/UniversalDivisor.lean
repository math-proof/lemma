import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties
import Structure.AlgebraicCurve_UniversalDivisor

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {k : Type u} [Field k]


@[ext] lemma RelEffDivisor.ext {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {D₁ D₂ : RelEffDivisor C c r T t}
    (h : D₁.I = D₂.I) : D₁ = D₂ := by
  cases D₁; cases D₂; cases h; rfl

lemma mapOnProd_fst {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    mapOnProd c φ hφ ≫ pullback.fst c csym = pullback.fst c t := by
  simp only [mapOnProd, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma mapOnProd_snd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    mapOnProd c φ hφ ≫ pullback.snd c csym = pullback.snd c t ≫ φ := by
  simp only [mapOnProd, pullback.map, pullback.lift_snd]

lemma isPullback_mapOnProd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    IsPullback (mapOnProd c φ hφ) (pullback.snd c t) (pullback.snd c csym) φ := by
  subst hφ
  refine IsPullback.of_right (h₁₂ := pullback.fst c csym) (v₁₃ := c) (h₂₂ := csym) ?_
    (mapOnProd_snd c φ rfl) (IsPullback.of_hasPullback c csym)
  simpa using IsPullback.of_hasPullback c (φ ≫ csym)


section transport

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}

noncomputable def comapSubschemeMap (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) : (I.comap (mapOnProd c φ hφ)).subscheme ⟶ I.subscheme :=
  (I.comapIso (mapOnProd c φ hφ)).hom ≫ pullback.snd _ _

lemma isPullback_comapSubschemeMap (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) :
    IsPullback (comapSubschemeMap I φ hφ) (I.comap (mapOnProd c φ hφ)).subschemeι
      I.subschemeι (mapOnProd c φ hφ) := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso (mapOnProd c φ hφ)) ?_ ?_).flip
  · simp [comapSubschemeMap]
  · simp
  · simp [comapSubschemeMap]

lemma isPullback_comap_snd (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) :
    IsPullback (comapSubschemeMap I φ hφ)
      ((I.comap (mapOnProd c φ hφ)).subschemeι ≫ pullback.snd c t)
      (I.subschemeι ≫ pullback.snd c csym) φ :=
  (isPullback_comapSubschemeMap I φ hφ).paste_vert (isPullback_mapOnProd c φ hφ)

end transport

noncomputable def RelEffDivisor.pullbackAlong {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) : RelEffDivisor C c r T t where
  I := Dcan.I.comap (mapOnProd c φ hφ)
  isFinite :=
    have := Dcan.isFinite
    MorphismProperty.of_isPullback (isPullback_comap_snd Dcan.I φ hφ) ‹_›
  flat :=
    have := Dcan.flat
    MorphismProperty.of_isPullback (isPullback_comap_snd Dcan.I φ hφ) ‹_›
  finrank_eq s := by
    have := Dcan.isFinite
    have := Dcan.flat
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_comap_snd Dcan.I φ hφ) s]
    exact Dcan.finrank_eq (φ s)

theorem pullsBack_pullbackAlong {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) :
    PullsBack Dcan φ hφ (Dcan.pullbackAlong φ hφ) := rfl

lemma PullsBack.eq_pullbackAlong {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {Dcan : RelEffDivisor C c r Csym csym}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {φ : T ⟶ Csym}
    {hφ : φ ≫ csym = t} {D' : RelEffDivisor C c r T t} (h : PullsBack Dcan φ hφ D') :
    D' = Dcan.pullbackAlong φ hφ :=
  RelEffDivisor.ext h.symm

lemma PullsBack.isPullback {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {Dcan : RelEffDivisor C c r Csym csym}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {φ : T ⟶ Csym}
    {hφ : φ ≫ csym = t} {D' : RelEffDivisor C c r T t} (h : PullsBack Dcan φ hφ D') :
    ∃ ψ : D'.I.subscheme ⟶ Dcan.I.subscheme,
      IsPullback ψ (D'.I.subschemeι ≫ pullback.snd c t)
        (Dcan.I.subschemeι ≫ pullback.snd c csym) φ := by
  obtain rfl := h.eq_pullbackAlong
  exact ⟨_, isPullback_comap_snd Dcan.I φ hφ⟩

lemma RelEffDivisor.pullbackAlong_comp {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t)
    {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (φ' : T' ⟶ T)
    (hφ' : φ' ≫ t = t') :
    (Dcan.pullbackAlong φ hφ).pullbackAlong φ' hφ' =
      Dcan.pullbackAlong (φ' ≫ φ) (by rw [Category.assoc, hφ, hφ']) := by
  refine RelEffDivisor.ext ?_
  change (Dcan.I.comap _).comap _ = Dcan.I.comap _
  rw [← Scheme.IdealSheafData.comap_comp]
  congr 1
  ext <;> simp


end AlgebraicCurve
