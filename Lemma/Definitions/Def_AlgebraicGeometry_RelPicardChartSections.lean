import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Lemma.Definitions.Def_AlgebraicCurve_CurveModel
import Lemma.Definitions.Def_AlgebraicCurve_AdelicIndex

set_option autoImplicit false

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra AlgebraicCurve

universe u

noncomputable def sectionFibrePoint {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {k : Type u} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    {p : Spec (CommRingCat.of k) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _} :=
  ⟨pullback.lift (s ≫ γ.1) (𝟙 _) (by rw [Category.assoc, γ.2, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

def ChartSectionsAt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {n g r : ℕ} (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    {L : Type u} [Field L] [Algebra k L] (M : CurveModel k L)
    (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase) : Prop :=
  (∃ Kc : Divisor k L, ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) ∧
  ∀ D : Divisor k L, (∀ v, 0 ≤ D v) → Divisor.degree D = r →
    ∃ i : Fin n, ell (D - ∑ j : Fin (r - g),
      Finsupp.single (M.pointEquivPlace
        ⟨(sectionFibrePoint (γ i j) s).1 ≫ e.inv, by
          rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (sectionFibrePoint (γ i j) s).2⟩) 1) = 1

def HasChartSections {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {n g r : ℕ} (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (M : CurveModel k L)
      (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase), ChartSectionsAt γ s M e he

def HasChartSectionsOverClosedPoints {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {n g r : ℕ} (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
    IsClosed ({s.base (IsLocalRing.closedPoint k)} : Set (Spec (CommRingCat.of R))) →
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (M : CurveModel k L)
      (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase), ChartSectionsAt γ s M e he

end AlgebraicGeometry.RelPicard
