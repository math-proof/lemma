import Lemma.Measure.ProductionPinsCompact
import Def.AutomorphicForm_ArithCuspRealization
import Lemma.UpperHalfPlane.SiegelCovering

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix Measure
open Measure.AdelicHaar Matrix.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel UpperHalfPlane.SiegelCovering Ideal Measure UpperHalfPlane
open Matrix.SiegelVolume

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

open scoped nonZeroDivisors in

noncomputable def finIdeleExponentAt (v : HeightOneSpectrum (𝓞 F))
    (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) : ℤ :=
  -WithZero.log (Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v))

open scoped nonZeroDivisors in

noncomputable def finAssocFracIdeal (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    FractionalIdeal (𝓞 F)⁰ F :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ finIdeleExponentAt F v δ

open scoped nonZeroDivisors in
open scoped nonZeroDivisors in
open scoped nonZeroDivisors in
open scoped nonZeroDivisors Classical in
open scoped nonZeroDivisors in

noncomputable def contentHomFin : (FiniteAdeleRing (𝓞 F) F)ˣ →* ClassGroup (𝓞 F) where
  toFun δ := ClassGroup.mk F (Units.mk0 (finAssocFracIdeal F δ) (finAssocFracIdeal_ne_zero F δ))
  map_one' := by
    rw [← map_one (ClassGroup.mk (R := 𝓞 F) (K := F))]
    congr 1
    refine Units.ext ?_
    simp only [Units.val_mk0, Units.val_one, finAssocFracIdeal]
    exact finprod_eq_one_of_forall_eq_one fun v => by rw [finIdeleExponentAt_one, zpow_zero]
  map_mul' δ₁ δ₂ := by
    rw [← map_mul]
    congr 1
    exact Units.ext (by simpa using finAssocFracIdeal_mul F δ₁ δ₂)

open scoped nonZeroDivisors in
open scoped nonZeroDivisors Classical in

def classSq : ClassGroup (𝓞 F) →* ClassGroup (𝓞 F) := powMonoidHom 2

omit [NumberField F] in
open scoped Classical in

noncomputable def classRepFinIdele (C : ClassGroup (𝓞 F) ⧸ (classSq F).range) :
    (FiniteAdeleRing (𝓞 F) F)ˣ :=
  if C = 1 then 1
  else Function.surjInv
    ((QuotientGroup.mk'_surjective (classSq F).range).comp (contentHomFin_surjective F)) C

noncomputable def finIdeleDiag : (FiniteAdeleRing (𝓞 F) F)ˣ →* AdelicGL2 (𝓞 F) F :=
  diagOne.comp (Units.map (finIncl (𝓞 F) F))

noncomputable def classRepEmbedding :
    (ClassGroup (𝓞 F) ⧸ (classSq F).range) ↪ AdelicGL2 (𝓞 F) F :=
  ⟨fun C => finIdeleDiag F (classRepFinIdele F C),
    (injective_finIdeleDiag F).comp (Function.LeftInverse.injective
      (g := fun δ => QuotientGroup.mk' (classSq F).range (contentHomFin F δ))
      (classRepFinIdele_spec F))⟩

noncomputable def classRepTranslates : Finset (AdelicGL2 (𝓞 F) F) :=
  haveI := Fintype.ofFinite (ClassGroup (𝓞 F) ⧸ (classSq F).range)
  Finset.univ.map (classRepEmbedding F)

noncomputable def classRepSiegelSet (c u d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  ⋃ x ∈ classRepTranslates F, (· * x) '' centreCutSiegelSet F c u d₁ d₂

def productionPinsGeneralOf (c u d₁ d₂ : ℝ) (_hd : d₁ < d₂) : CarrierPins F :=
  productionPinsOf F
    (classRepSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

def productionPinsGeneral : CarrierPins F :=
  productionPinsGeneralOf F (1/2 : ℝ) 1 (1/2) 2 (by norm_num)

def IsGenuineCuspRealizationAt (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F pins Φ) : Prop :=
  Continuous R.toFun

def IsGenuineCuspRealizable (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) : Prop :=
  ∃ R : SmoothCuspRealizationAt F pins Φ, IsGenuineCuspRealizationAt F pins Φ R

def IsArithGenuineCuspRealizable (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) : Prop :=
  IsGenuineCuspRealizable F pins Φ.toRawCentral

def IsArithGenuineCuspRealizableVia (pins : CarrierPins F) {R : Type*} [CommRing R]
    (ι : R →+* ℂ) (Φ : HeckeEigensystem F R) : Prop :=
  IsArithGenuineCuspRealizable F pins (Φ.map ι)

def genuineCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ => @IsArithGenuineCuspRealizable F _i1 _i2 (pins F) Φ

end AutomorphicForm

end

section Battery
open AutomorphicForm Ideal Measure UpperHalfPlane
#check @finIdeleExponentAt
#check @finAssocFracIdeal
#check @contentHomFin
#check @contentHomFin_apply
#check @contentHomFin_surjective
#check @classSq
#check @classRepFinIdele
#check @classRepFinIdele_spec
#check @finIdeleDiag
#check @classRepEmbedding
#check @classRepEmbedding_apply
#check @classRepSiegelSet
#check @card_classRepTranslates
#check @productionPinsGeneralOf
#check @productionPinsGeneral
#check @IsGenuineCuspRealizationAt
#check @IsGenuineCuspRealizable
#check @IsArithGenuineCuspRealizable
#check @IsArithGenuineCuspRealizableVia
#check @genuineCuspNotionOf
#print axioms AutomorphicForm.finAssocFracIdeal_ne_zero
#print axioms AutomorphicForm.count_finAssocFracIdeal
#print axioms AutomorphicForm.finAssocFracIdeal_mul
#print axioms AutomorphicForm.finIdeleExponentAt_localUnit_uniformizer
#print axioms AutomorphicForm.contentHomFin_surjective
#print axioms AutomorphicForm.classRepFinIdele_spec
#print axioms AutomorphicForm.glArch_finIdeleDiag
#print axioms AutomorphicForm.injective_finIdeleDiag
#print axioms AutomorphicForm.glArch_classRepEmbedding
#print axioms AutomorphicForm.classRepEmbedding_one
#print axioms AutomorphicForm.productionPinsGeneral_eq_compact_of_odd
#print axioms AutomorphicForm.IsGenuineCuspRealizable.isSmoothCuspRealizable
#print axioms AutomorphicForm.classRepSiegelSet_eq_of_odd
#print axioms AutomorphicForm.card_classRepTranslates
#print axioms AutomorphicForm.one_mem_classRepTranslates
#print axioms AutomorphicForm.classRepTranslates_eq_singleton_one_of_odd
#print axioms AutomorphicForm.not_ae_zero_restrict_of_continuous_of_mem_interior
#print axioms AutomorphicForm.productionPinsGeneral_μ_D_pos_lt_top
end Battery
