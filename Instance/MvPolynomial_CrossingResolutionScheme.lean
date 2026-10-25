-- Carved from Lemma/Definitions/Def_MvPolynomial_CrossingResolutionScheme.lean: instance decls only.
import Mathlib
import Lemma.MvPolynomial.CrossingResolution
import Inductive.MvPolynomial_GlueIndex
import Lemma.MvPolynomial.CrossingResolutionScheme

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type u} [CommRing W] (t : W)

instance isLocalization_away_torusRing :
    IsLocalization.Away (algebraMap W (CrossingQuotient W t) t) (TorusRing t) := by
  rw [← U_mul_V]; infer_instance

variable {t}

variable (t)


section spectra

instance isOpenImmersion_overlapToChartRight : IsOpenImmersion (overlapToChartRight t) := by
  have H : IsIso (CommRingCat.ofHom (transitionEquiv t).toRingHom) :=
    inferInstanceAs (IsIso (transitionEquiv t).toCommRingCatIso.hom)
  rw [overlapToChartRight, ← toRingHom_transitionEquiv_comp, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

instance isOpenImmersion_torusToChart (i : ℕ) : IsOpenImmersion (torusToChart t i) := by
  have := isIso_ofHom_twistEquiv t i
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient W t) (TorusRing t)))) :=
    IsOpenImmersion.of_isLocalization (algebraMap W (CrossingQuotient W t) t)
  rw [torusToChart_eq]
  infer_instance

instance isOpenImmersion_torusToOverlap (i : ℕ) : IsOpenImmersion (torusToOverlap t i) := by
  have := isIso_ofHom_twistEquiv t i
  rw [torusToOverlap_eq]
  infer_instance

end spectra

namespace GlueIndex

variable {e : ℕ}

instance : LE (GlueIndex e) := ⟨GlueIndex.le⟩

instance : Preorder (GlueIndex e) where
  le_refl a := by cases a <;> simp
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;>
      simp only [torus_le, overlap_le_overlap, overlap_le_chart, chart_le_chart, overlap_le_torus,
        chart_le_torus, chart_le_overlap] at hab hbc ⊢ <;> subst_vars <;> simp_all

end GlueIndex

open GlueIndex

section diagram

variable (e : ℕ)

instance isOpenImmersion_glueMap (a b : GlueIndex e) (hab : a ≤ b) :
    IsOpenImmersion (glueMap t e a b hab) := by
  cases a <;> cases b <;>
    simp only [torus_le, overlap_le_overlap, overlap_le_chart, chart_le_chart, overlap_le_torus,
      chart_le_torus, chart_le_overlap] at hab
  case overlap.chart =>
    rename_i i hi j hab0
    by_cases h : (j : ℕ) = i
    · rw [glueMap_overlap_chart_of_eq t e hi _ h]
      exact inferInstanceAs (IsOpenImmersion (overlapToChartLeft t))
    · rw [glueMap_overlap_chart_of_ne t e hi _ h]
      exact inferInstanceAs (IsOpenImmersion (overlapToChartRight t))
  case torus.torus => exact inferInstanceAs (IsOpenImmersion (𝟙 (torusScheme t)))
  case torus.overlap h i hi hab0 => exact inferInstanceAs (IsOpenImmersion (torusToOverlap t i))
  case torus.chart h j hab0 => exact inferInstanceAs (IsOpenImmersion (torusToChart t j))
  case overlap.overlap => exact inferInstanceAs (IsOpenImmersion (𝟙 (overlapScheme t)))
  case chart.chart => exact inferInstanceAs (IsOpenImmersion (𝟙 (chartScheme t)))

instance isOpenImmersion_glueDiagram_map {a b : GlueIndex e} (f : a ⟶ b) :
    IsOpenImmersion ((glueDiagram t e).map f) :=
  isOpenImmersion_glueMap t e a b f.le

end diagram

section locallyDirected

variable (e : ℕ)

variable {e}

instance isLocallyDirected_glueDiagram : (glueDiagram t e ⋙ Scheme.forget).IsLocallyDirected where
  cond fa fb xa xb h := glue_cond t fa fb xa xb h

end locallyDirected

section scheme

variable (e : ℕ)

namespace Resolution

instance isOpenImmersion_ι (i : Fin e) : IsOpenImmersion (ι t e i) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram t e) (chart i)))

instance isOpenImmersion_ιOverlap (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    IsOpenImmersion (ιOverlap t e i hi) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram t e) (overlap i hi)))

instance isOpenImmersion_ιTorus (h : 0 < e) : IsOpenImmersion (ιTorus t e h) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (glueDiagram t e) (torus h)))

instance (i : (openCover t e).I₀) : IsAffine ((openCover t e).X i) :=
  inferInstanceAs (IsAffine (chartScheme t))

end Resolution

end scheme

end CrossingQuotient

end MvPolynomial

end
