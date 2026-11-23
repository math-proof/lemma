import Mathlib
import Def.MvPolynomial_CrossingResolution
import Inductive.MvPolynomial_GlueIndex
import Instance.MvPolynomial_CrossingResolutionScheme
import Abbrev.MvPolynomial_CrossingResolutionScheme

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type u} [CommRing W] (t : W)

def twist₀ (a b : TorusRing t) (hab : a * b = 1) : CrossingQuotient W t →ₐ[W] TorusRing t :=
  lift t (xT t * a) (yT t * b) (by rw [mul_mul_mul_comm, xT_mul_yT, hab, mul_one])

def twistRingHom (a b : TorusRing t) (hab : a * b = 1) : TorusRing t →+* TorusRing t :=
  IsLocalization.Away.lift (S := TorusRing t) (algebraMap W (CrossingQuotient W t) t)
    (g := (twist₀ t a b hab).toRingHom) (isUnit_twist₀_apply t a b hab)

def twist (a b : TorusRing t) (hab : a * b = 1) : TorusRing t →ₐ[W] TorusRing t :=
  { twistRingHom t a b hab with
    commutes' := fun w => by
      change twistRingHom t a b hab (algebraMap W (TorusRing t) w) = _
      rw [IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (TorusRing t) w,
        twistRingHom_algebraMap]
      exact (twist₀ t a b hab).commutes w }

variable {t}

variable (t)

def twistEquiv (i : ℕ) : TorusRing t ≃ₐ[W] TorusRing t :=
  AlgEquiv.ofAlgHom (twist t (tinv t ^ i) (tT t ^ i) (tinv_pow_mul_tT_pow t i))
    (twist t (tT t ^ i) (tinv t ^ i) (tT_pow_mul_tinv_pow t i))
    (twist_comp_twist _ _ _ (twist_tinv_pow _ _ _ i) (twist_tT_pow _ _ _ i))
    (twist_comp_twist _ _ _ (twist_tT_pow _ _ _ i) (twist_tinv_pow _ _ _ i))

def torusChart (i : ℕ) : CrossingQuotient W t →ₐ[W] TorusRing t :=
  (twistEquiv t i).toAlgHom.comp (IsScalarTower.toAlgHom W (CrossingQuotient W t) (TorusRing t))

def torusOverlap (i : ℕ) : OverlapRing t →ₐ[W] TorusRing t :=
  (twistEquiv t i).toAlgHom.comp (IsScalarTower.toAlgHom W (OverlapRing t) (TorusRing t))

section transition

def transitionUpAway : Localization.Away (U t) →+* OverlapRing t :=
  IsLocalization.Away.lift (S := Localization.Away (U t)) (U t) (g := (transitionUp t).toRingHom)
    (by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, transitionUp_U]
      exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (V t)))

def transitionDownAway : OverlapRing t →+* Localization.Away (U t) :=
  IsLocalization.Away.lift (S := OverlapRing t) (V t) (g := (transitionDown t).toRingHom)
    (by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, transitionDown_V]
      exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (U t)))

def transitionEquiv : Localization.Away (U t) ≃+* OverlapRing t :=
  RingEquiv.ofRingHom (transitionUpAway t) (transitionDownAway t)
    (transitionUpAway_comp_transitionDownAway t) (transitionDownAway_comp_transitionUpAway t)

end transition

section spectra

abbrev torusToChart (i : ℕ) : torusScheme t ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (torusChart t i).toRingHom)

abbrev torusToOverlap (i : ℕ) : torusScheme t ⟶ overlapScheme t :=
  Spec.map (CommRingCat.ofHom (torusOverlap t i).toRingHom)

end spectra

namespace GlueIndex

variable {e : ℕ}

protected def le : GlueIndex e → GlueIndex e → Prop
  | torus _, _ => True
  | overlap i _, overlap j _ => i = j
  | overlap i _, chart j => j = i ∨ (j : ℕ) = i + 1
  | chart i, chart j => i = j
  | overlap _ _, torus _ => False
  | chart _, torus _ => False
  | chart _, overlap _ _ => False

end GlueIndex

open GlueIndex

section diagram

variable (e : ℕ)

def glueObj : GlueIndex e → Scheme.{u}
  | .chart _ => chartScheme t
  | .overlap _ _ => overlapScheme t
  | .torus _ => torusScheme t

def glueMap : ∀ a b : GlueIndex e, a ≤ b → (glueObj t e a ⟶ glueObj t e b)
  | .torus _, .torus _, _ => 𝟙 _
  | .torus _, .overlap i _, _ => torusToOverlap t i
  | .torus _, .chart j, _ => torusToChart t j
  | .overlap _ _, .overlap _ _, _ => 𝟙 _
  | .overlap i _, .chart j, _ =>
      if (j : ℕ) = i then overlapToChartLeft t else overlapToChartRight t
  | .chart _, .chart _, _ => 𝟙 _
  | .overlap _ _, .torus _, h => False.elim h
  | .chart _, .torus _, h => False.elim h
  | .chart _, .overlap _ _, h => False.elim h

def glueDiagram : GlueIndex e ⥤ Scheme.{u} where
  obj := glueObj t e
  map f := glueMap t e _ _ f.le
  map_id a := glueMap_id t e a
  map_comp f g := glueMap_comp t e _ _ _ f.le g.le

end diagram


section scheme

variable (e : ℕ)

def Resolution : Scheme.{u} := colimit (glueDiagram t e)

namespace Resolution

def ι (i : Fin e) : chartScheme t ⟶ Resolution t e := colimit.ι (glueDiagram t e) (chart i)

def ιOverlap (i : Fin e) (hi : (i : ℕ) + 1 < e) : overlapScheme t ⟶ Resolution t e :=
  colimit.ι (glueDiagram t e) (overlap i hi)

def ιTorus (h : 0 < e) : torusScheme t ⟶ Resolution t e := colimit.ι (glueDiagram t e) (torus h)

def openCover : (Resolution t e).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin e) (fun _ => chartScheme t) (ι t e) (exists_ι_apply_eq t e)

abbrev chartToCrossing (i : Fin e) : chartScheme t ⟶ crossingScheme (t ^ e) :=
  Spec.map (CommRingCat.ofHom (resolutionChart t e i).toRingHom)

def crossingCoconeApp : ∀ a : GlueIndex e, (glueObj t e a ⟶ crossingScheme (t ^ e))
  | .chart j => chartToCrossing t e j
  | .overlap i _ => overlapToChartLeft t ≫ chartToCrossing t e i
  | .torus h => torusToChart t (0 : ℕ) ≫ chartToCrossing t e ⟨0, h⟩

def crossingCocone : Cocone (glueDiagram t e) where
  pt := crossingScheme (t ^ e)
  ι := { app := crossingCoconeApp t e
         naturality := fun a b f =>
           (glueMap_crossingCoconeApp t e a b f.le).trans (Category.comp_id _).symm }

def toCrossing : Resolution t e ⟶ crossingScheme (t ^ e) := colimit.desc (glueDiagram t e) (crossingCocone t e)

def toSpec : Resolution t e ⟶ Spec (CommRingCat.of W) :=
  toCrossing t e ≫ Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W (t ^ e))))

end Resolution

end scheme

end CrossingQuotient

end MvPolynomial

end
