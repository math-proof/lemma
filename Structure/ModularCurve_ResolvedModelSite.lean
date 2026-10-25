import Mathlib
import Lemma.AlgebraicGeometry.ResolvedModelGlueComponents
import Structure.ModularCurve_DRResolvedModelPackageV4
import Abbrev.ModularCurve_DRModelPackage
import Instance.MvPolynomial_CrossingResolutionScheme
import Instance.MvPolynomial_CrossingResolutionFibrePoints

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Glue.SiteAux


end V3Glue.SiteAux

end

noncomputable section

namespace V3Glue.Site

open ModularCurve MvPolynomial MvPolynomial.CrossingQuotient

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]

abbrev XO : Scheme.{0} := pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))

abbrev Node : Type := ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))

variable (bc : pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶ XO p O)

variable {p O κ} in

abbrev xpt (n : Node p 𝔛 κ) : XO p O :=
  (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base n

def HasOrientedCrossingCharts : Prop :=
    ∀ n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      ∃ (e : ℕ) (_ : 1 ≤ e)
        (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens)
        (_ : (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base n ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base n) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ bc).base n →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.compInf κ ≫ bc).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.compZero κ ≫ bc).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.compInf κ ≫ bc).base →
            CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.compZero κ ≫ bc).base →
            CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)

structure ModelHyps : Prop where

  L6 : ∀ e : ℕ, 0 < e → IsIso (Resolution.toCrossing ((p : ℕ) : O) e ∣_
    (PrimeSpectrum.basicOpen (CrossingQuotient.U (((p : ℕ) : O) ^ e)) ⊔ PrimeSpectrum.basicOpen (CrossingQuotient.V (((p : ℕ) : O) ^ e))))

  P6 : ∀ e : ℕ, IsProper (Resolution.toCrossing ((p : ℕ) : O) e)

  flat : ∀ e : ℕ, Flat (Resolution.toCrossing ((p : ℕ) : O) e ≫
    Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))))

  noeth : ∀ e : ℕ, IsLocallyNoetherian (Resolution ((p : ℕ) : O) e)

  interior : ∀ e : ℕ, interior ((Resolution.toCrossing ((p : ℕ) : O) e).base ⁻¹'
    ((PrimeSpectrum.basicOpen (CrossingQuotient.U (((p : ℕ) : O) ^ e)) ⊔
      PrimeSpectrum.basicOpen (CrossingQuotient.V (((p : ℕ) : O) ^ e)) : (crossingScheme (((p : ℕ) : O) ^ e)).Opens) :
        Set (crossingScheme (((p : ℕ) : O) ^ e)))ᶜ) = ∅

def EtNbhd : Prop :=
  ∀ {U S : Scheme.{0}} (f : U ⟶ S) [LocallyOfFinitePresentation f] (x : U),
    (f.stalkMap x).hom.Flat →
    Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base x))) =
      IsLocalRing.maximalIdeal (U.presheaf.stalk x) →
    ∀ [IsIso (f.residueFieldMap x)], ∃ V : U.Opens, x ∈ V ∧ Etale (V.ι ≫ f)

structure ChartData (n : Node p 𝔛 κ) where
  e : ℕ
  one_le_e : 1 ≤ e
  U : (XO p O).Opens
  x_mem_U : xpt 𝔛 bc n ∈ U
  f : (U : Scheme.{0}) ⟶ crossingScheme (((p : ℕ) : O) ^ e)
  f_over : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _
  f_fibre : ∀ y : ↥(U : Scheme.{0}),
    (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔
      U.ι.base y = xpt 𝔛 bc n
  f_node : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = xpt 𝔛 bc n →
    (f.stalkMap y).hom.Flat ∧
      Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y)

  orient_inf : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
    U.ι.base y ∈ Set.range (𝔛.compInf κ ≫ bc).base

  orient_zero : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
    U.ι.base y ∈ Set.range (𝔛.compZero κ ≫ bc).base

  orient_inf_conv : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.compInf κ ≫ bc).base →
    CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal
  orient_zero_conv : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.compZero κ ≫ bc).base →
    CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal


end V3Glue.Site

end

noncomputable section

namespace V3Asm

open ModularCurve MvPolynomial MvPolynomial.CrossingQuotient

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)


structure SiteHyps : Prop where
  nodeFinite : Finite (V3Glue.Site.Node p 𝔛 κ)
  hC : V3Glue.Site.HasOrientedCrossingCharts p 𝔛 O κ (bc p O κ toκ)
  ET : V3Glue.Site.EtNbhd
  hxinj : Function.Injective (fun n : V3Glue.Site.Node p 𝔛 κ => V3Glue.Site.xpt 𝔛 (bc p O κ toκ) n)
  hxcl : ∀ n : V3Glue.Site.Node p 𝔛 κ, IsClosed ({V3Glue.Site.xpt 𝔛 (bc p O κ toκ) n} : Set (V3Glue.Site.XO p O))
  model : V3Glue.Site.ModelHyps p O

variable (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) (H : SiteHyps p 𝔛 O κ toκ)


def toDR : Y p 𝔛 O κ toκ hϖ H ⟶ V3Glue.Site.XO p O := (D p 𝔛 O κ toκ hϖ H).toDR
def toBase : Y p 𝔛 O κ toκ hϖ H ⟶ Spec (CommRingCat.of O) := toDR p 𝔛 O κ toκ hϖ H ≫ πX p O


variable (hξ : ∀ j, ξ p 𝔛 O κ toκ j ∈ (C p 𝔛 O κ toκ hϖ H).X0)


end V3Asm

end
