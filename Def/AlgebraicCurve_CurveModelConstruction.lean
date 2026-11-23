import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Def.AlgebraicCurve_CurveModel
import Instance.JacJ1_ChartAlgebra
import Lemma.Set.CurveModelSmooth
import Instance.AlgebraicCurve_CurveModelConstruction
import Abbrev.AlgebraicCurve_CurveModelConstruction

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IntermediateField IsDedekindDomain
open Topology TopCat

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)

section Charts

abbrev incl₀ : chartRing K ({t} : Set L) →ₐ[K] chartRing K ({t, t⁻¹} : Set L) :=
  chartIncl K (singleton_subset_pair t)

abbrev inclInf : chartRing K ({t⁻¹} : Set L) →ₐ[K] chartRing K ({t, t⁻¹} : Set L) :=
  chartIncl K (singleton_inv_subset_pair t)

def tChart : chartRing K ({t} : Set L) := ⟨t, subset_chartRing K {t} (Set.mem_singleton t)⟩

def tInvChart : chartRing K ({t⁻¹} : Set L) :=
  ⟨t⁻¹, subset_chartRing K {t⁻¹} (Set.mem_singleton t⁻¹)⟩

abbrev f₀ : XOverlap K t ⟶ X₀ K t := Spec.map (CommRingCat.ofHom (incl₀ K t).toRingHom)

abbrev fInf : XOverlap K t ⟶ XInf K t := Spec.map (CommRingCat.ofHom (inclInf K t).toRingHom)

variable [Fact (t ≠ 0)]

end Charts

section Glue

variable [Fact (t ≠ 0)]

def glued : Scheme.{u} := pushout (f₀ K t) (fInf K t)

def ι₀ : X₀ K t ⟶ glued K t := pushout.inl (f₀ K t) (fInf K t)

def ιInf : XInf K t ⟶ glued K t := pushout.inr (f₀ K t) (fInf K t)

def gluedToBase : glued K t ⟶ Spec (CommRingCat.of K) :=
  pushout.desc (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t} : Set L)))))
    (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K ({t⁻¹} : Set L)))))
    (f₀_toBase_eq_fInf_toBase K t)

end Glue

section Qualities

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

def overlapFunctionFieldAlgEquiv :
    L ≃ₐ[chartRing K ({t, t⁻¹} : Set L)] (XOverlap K t).functionField :=
  IsLocalization.algEquiv (nonZeroDivisors (chartRing K ({t, t⁻¹} : Set L))) L _

def ιU : XOverlap K t ⟶ glued K t := f₀ K t ≫ ι₀ K t

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in
def gluedFunctionFieldIsoOverlap :
    (glued K t).functionField ≅ (XOverlap K t).functionField :=
  (glued K t).presheaf.stalkCongr (.of_eq (ιU_genericPoint K t).symm) ≪≫
    asIso ((ιU K t).stalkMap (genericPoint (XOverlap K t)))

def gluedFunctionFieldEquiv : L ≃+* (glued K t).functionField :=
  (overlapFunctionFieldAlgEquiv K t).toRingEquiv.trans
    (gluedFunctionFieldIsoOverlap K t).commRingCatIsoToRingEquiv.symm

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

end Qualities


section StalkRange

variable [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]

variable (A : Subalgebra K L) (i : A →ₐ[K] chartRing K ({t, t⁻¹} : Set L))
  (hi : ∀ a : A, (i a : L) = a)
  (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom i.toRingHom))]
  (comm : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ιA = ιU K t)

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in

def thetaHom (p : Spec (CommRingCat.of A)) : (Spec (CommRingCat.of A)).presheaf.stalk p →+* L :=
  ((overlapFunctionFieldAlgEquiv K t).symm : (XOverlap K t).functionField →+* L).comp
    (((Spec.map (CommRingCat.ofHom i.toRingHom)).stalkMap (genericPoint (XOverlap K t))).hom.comp
      ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes
        (by rw [specMap_genericPoint]; exact genericPoint_specializes p)).hom)

include hi in
omit [Fact (t ≠ 0)] in

end StalkRange

section PlaceMap

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

omit [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in
def primeOfι₀ (ht : Transcendental K t) (x₀ : X₀ K t)
    (hx : (ι₀ K t).base x₀ ∈ closedPoints (glued K t)) :
    HeightOneSpectrum (chartRing K ({t} : Set L)) :=
  ⟨x₀.asIdeal, x₀.isPrime,
    (isMaximal_iff_ne_bot K t ht _).mp ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x₀).mp
      ((ι₀_mem_closedPoints_iff K t x₀).mp hx))⟩

def primeOfιInf (ht : Transcendental K t) (xi : XInf K t)
    (hx : (ιInf K t).base xi ∈ closedPoints (glued K t)) :
    HeightOneSpectrum (chartRing K ({t⁻¹} : Set L)) :=
  ⟨xi.asIdeal, xi.isPrime,
    (isMaximal_iff_ne_bot K t⁻¹ (transcendental_inv K t ht) _).mp
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal xi).mp
        ((ιInf_mem_closedPoints_iff K t xi).mp hx))⟩

open scoped Classical in

def gluedPlaceOfPoint (ht : Transcendental K t) (x : closedPoints (glued K t)) : Place K L :=
  if h : x.1 ∈ Set.range (ι₀ K t).base then
    Place.ofHeightOneSpectrum (K := K)
      (primeOfι₀ K t ht (Classical.choose h) (by rw [Classical.choose_spec h]; exact x.2))
  else
    Place.ofHeightOneSpectrum (K := K)
      (primeOfιInf K t ht (Classical.choose (mem_range_ιInf_of_not_mem_range_ι₀ K t h))
        (by rw [Classical.choose_spec (mem_range_ιInf_of_not_mem_range_ι₀ K t h)]; exact x.2))

end PlaceMap

open IsLocalRing


section RingLemmas

variable {B R F : Type*} [CommRing B] [CommRing R] [CommRing F]

def liftOfRange (j : R →+* F) (hj : Function.Injective j) (g : B →+* F)
    (h : ∀ b, g b ∈ j.range) : B →+* R :=
  (RingEquiv.ofBijective j.rangeRestrict
      ⟨fun _ _ e => hj (congrArg Subtype.val e), j.rangeRestrict_surjective⟩).symm.toRingHom.comp
    (g.codRestrict j.range h)

end RingLemmas


section Generic

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

variable (S : ValuativeCommSq (gluedToBase K t))
  (φ : (glued K t).presheaf.stalk (genericPoint (glued K t)) ⟶ CommRingCat.of S.K)

def gL : L →+* S.K := φ.hom.comp (gluedFunctionFieldEquiv K t).toRingHom

omit [CharZero K] [FiniteDimensional K⟮t⁻¹⟯ L] in
def pullbackVS : ValuationSubring L where
  toSubring := (algebraMap S.R S.K).range.comap (gL K t S φ)
  mem_or_inv_mem' y := by
    rcases ValuationRing.isInteger_or_isInteger S.R (gL K t S φ y) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r, hr⟩
    · exact Or.inr ⟨r, by rw [map_inv₀]; exact hr⟩

omit [CharZero K] [FiniteDimensional K⟮t⁻¹⟯ L] in
end Generic

section Closed

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

variable (A : Subalgebra K L) (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]
  (ιA_toBase : ιA ≫ gluedToBase K t = Spec.map (CommRingCat.ofHom (algebraMap K A)))
  (S : ValuativeCommSq (gluedToBase K t)) (p : Spec (CommRingCat.of A))
  (φ : (glued K t).presheaf.stalk (ιA.base p) ⟶ CommRingCat.of S.K)

def stalkChartEquiv :
    (glued K t).presheaf.stalk (ιA.base p) ≃+* (Spec (CommRingCat.of A)).presheaf.stalk p :=
  (asIso (ιA.stalkMap p)).commRingCatIsoToRingEquiv

def φA : (Spec (CommRingCat.of A)).presheaf.stalk p →+* S.K :=
  φ.hom.comp (stalkChartEquiv K t A ιA p).symm.toRingHom

def gA : A →+* S.K := (φA K t A ιA S p φ).comp (StructureSheaf.toStalk A p).hom

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in
variable [hmax : p.asIdeal.IsMaximal]

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] hmax in

end Closed

section ClosedLift

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

omit [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

end ClosedLift


open TopologicalSpace

section ChartGerms

variable (A : Subalgebra K L)

def secTop (r : A) : Γ(Spec (CommRingCat.of A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv r

variable [Fact (t ≠ 0)] (ιA : Spec (CommRingCat.of A) ⟶ glued K t) [IsOpenImmersion ιA]

def cSec (a : K) (W : (glued K t).Opens) : Γ(glued K t, W) :=
  (glued K t).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
    ((gluedToBase K t).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))

omit [IsOpenImmersion ιA] in

variable [FiniteDimensional K⟮t⟯ L]
variable (i : A →ₐ[K] chartRing K ({t, t⁻¹} : Set L)) (hi : ∀ a : A, (i a : L) = a)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom i.toRingHom))]
  (comm : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ιA = ιU K t)

include hi in
omit [Fact (t ≠ 0)] [IsOpenImmersion ιA] in
end ChartGerms

section LocalSections

variable (a : K)

def tma : chartRing K ({t} : Set L) := tChart K t - algebraMap K _ a

def gInf : chartRing K ({t⁻¹} : Set L) := 1 - algebraMap K _ a * tInvChart K t

def U₁ : (X₀ K t).Opens := (X₀ K t).basicOpen (secTop K (chartRing K ({t} : Set L)) (tma K t a))

def U₂ : (XInf K t).Opens :=
  (XInf K t).basicOpen (secTop K (chartRing K ({t⁻¹} : Set L)) (gInf K t a))

def σ₁ : Γ(X₀ K t, U₁ K t a) := (((isUnit_res_tma K t a).unit⁻¹ : (Γ(X₀ K t, U₁ K t a))ˣ) : _)

def σ₂ : Γ(XInf K t, U₂ K t a) :=
  (XInf K t).presheaf.map (homOfLE (le_top : U₂ K t a ≤ ⊤)).op
      (secTop K (chartRing K ({t⁻¹} : Set L)) (tInvChart K t)) *
    (((isUnit_res_gInf K t a).unit⁻¹ : (Γ(XInf K t, U₂ K t a))ˣ) : _)

end LocalSections

section Values

variable [Fact (t ≠ 0)] (a : K)

def V₁ : (glued K t).Opens := ι₀ K t ''ᵁ U₁ K t a

def V₂ : (glued K t).Opens := ιInf K t ''ᵁ U₂ K t a

def Ua : (glued K t).Opens := V₁ K t a ⊔ V₂ K t a

def f₁' : Γ(glued K t, V₁ K t a) := ((ι₀ K t).appIso (U₁ K t a)).inv (σ₁ K t a)

def f₂' : Γ(glued K t, V₂ K t a) := ((ιInf K t).appIso (U₂ K t a)).inv (σ₂ K t a)

variable (ha : (t - algebraMap K L a) ≠ 0)

include ha in
omit [Fact (t ≠ 0)] in
variable [FiniteDimensional K⟮t⟯ L]

include ha in

def cover : Bool → (glued K t).Opens := fun b => cond b (V₁ K t a) (V₂ K t a)

include ha in

end Values

section Affine

variable [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] (a : K) (ha : (t - algebraMap K L a) ≠ 0)

omit [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] in

variable (f : Γ(glued K t, Ua K t a))
  (hf₁ : (glued K t).presheaf.map (homOfLE (le_sup_left : V₁ K t a ≤ Ua K t a)).op f = f₁' K t a)
  (hf₂ : (glued K t).presheaf.map (homOfLE (le_sup_right : V₂ K t a ≤ Ua K t a)).op f = f₂' K t a)

def fTwo : Γ(glued K t, Ua K t a) := 1 + cSec K t a (Ua K t a) * f

omit [FiniteDimensional K⟮t⟯ L] in
end Affine

section Packaging

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]

variable [FiniteDimensional K⟮t⁻¹⟯ L]

def ofGenerator (ht : Transcendental K t) : CurveModel K L :=
  haveI := smoothOfRelativeDimension_one_gluedToBase K t ht
  { C := glued K t
    toBase := gluedToBase K t
    ffEquiv := gluedFunctionFieldEquiv K t
    ffEquiv_algebraMap := gluedFunctionFieldEquiv_algebraMap K t
    placeOfPoint := gluedPlaceOfPoint K t ht
    placeOfPoint_bijective := gluedPlaceOfPoint_bijective K t ht
    range_stalk_eq := range_stalk_eq_gluedPlaceOfPoint K t ht
    finset_subset_affineOpen := finset_subset_affineOpen_glued K t }

end Packaging

section TowerPack

variable [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]

def towerGenerator : L := algebraMap (RatFunc K) L RatFunc.X

omit [Algebra K L] [IsScalarTower K (RatFunc K) L] in
end TowerPack

end CurveModel

end AlgebraicCurve

end
