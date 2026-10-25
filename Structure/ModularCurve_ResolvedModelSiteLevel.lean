import Mathlib
import Lemma.AlgebraicGeometry.ResolvedModelGlueComponents
import Structure.ModularCurve_DRResolvedModelPackageLevel
import Abbrev.ModularCurve_DRModelPackageLevel
import Lemma.Scheme.DRModelPackageLevelAPI
import Instance.MvPolynomial_CrossingResolutionScheme
import Instance.MvPolynomial_CrossingResolutionFibrePoints

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Glue.LevelSiteAux


end V3Glue.LevelSiteAux

end

noncomputable section

namespace V3Glue.LevelSite

open ModularCurve MvPolynomial MvPolynomial.CrossingQuotient

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (τ : DRLevel.R q →+* κ)

abbrev Node : Type := ↥(pullback (𝔛.comp κ τ 0) (𝔛.comp κ τ 1))

variable (bc : DRLevel.fibre (N₀ := N₀) τ ⟶ DRLevel.XO (N₀ := N₀) ρO)

variable {O ρO κ τ} in

abbrev xpt (n : Node 𝔛 κ τ) : DRLevel.XO (N₀ := N₀) ρO :=
  (pullback.fst (𝔛.comp κ τ 0) (𝔛.comp κ τ 1) ≫ 𝔛.comp κ τ 0 ≫ bc).base n

def HasOrientedCrossingCharts : Prop :=
    ∀ n : ↥(pullback (𝔛.comp κ τ 0) (𝔛.comp κ τ 1)),
      ∃ (e : ℕ) (_ : 1 ≤ e)
        (U : (DRLevel.XO (N₀ := N₀) ρO).Opens)
        (_ : (pullback.fst (𝔛.comp κ τ 0) (𝔛.comp κ τ 1) ≫ 𝔛.comp κ τ 0 ≫ bc).base n ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((q : ℕ) : O) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst (𝔛.comp κ τ 0) (𝔛.comp κ τ 1) ≫ 𝔛.comp κ τ 0 ≫ bc).base n) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp κ τ 0) (𝔛.comp κ τ 1) ≫ 𝔛.comp κ τ 0 ≫ bc).base n →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.comp κ τ 0 ≫ bc).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.comp κ τ 1 ≫ bc).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp κ τ 0 ≫ bc).base →
            CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp κ τ 1 ≫ bc).base →
            CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)

variable (q) in
omit [Fact q.Prime] in

structure ModelHyps : Prop where

  L6 : ∀ e : ℕ, 0 < e → IsIso (Resolution.toCrossing ((q : ℕ) : O) e ∣_
    (PrimeSpectrum.basicOpen (CrossingQuotient.U (((q : ℕ) : O) ^ e)) ⊔ PrimeSpectrum.basicOpen (CrossingQuotient.V (((q : ℕ) : O) ^ e))))

  P6 : ∀ e : ℕ, IsProper (Resolution.toCrossing ((q : ℕ) : O) e)

  flat : ∀ e : ℕ, Flat (Resolution.toCrossing ((q : ℕ) : O) e ≫
    Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ e)))))

  noeth : ∀ e : ℕ, IsLocallyNoetherian (Resolution ((q : ℕ) : O) e)

  interior : ∀ e : ℕ, interior ((Resolution.toCrossing ((q : ℕ) : O) e).base ⁻¹'
    ((PrimeSpectrum.basicOpen (CrossingQuotient.U (((q : ℕ) : O) ^ e)) ⊔
      PrimeSpectrum.basicOpen (CrossingQuotient.V (((q : ℕ) : O) ^ e)) : (crossingScheme (((q : ℕ) : O) ^ e)).Opens) :
        Set (crossingScheme (((q : ℕ) : O) ^ e)))ᶜ) = ∅

def EtNbhd : Prop :=
  ∀ {U S : Scheme.{0}} (f : U ⟶ S) [LocallyOfFinitePresentation f] (x : U),
    (f.stalkMap x).hom.Flat →
    Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base x))) =
      IsLocalRing.maximalIdeal (U.presheaf.stalk x) →
    ∀ [IsIso (f.residueFieldMap x)], ∃ V : U.Opens, x ∈ V ∧ Etale (V.ι ≫ f)

structure ChartData (n : Node 𝔛 κ τ) where
  e : ℕ
  one_le_e : 1 ≤ e
  U : (DRLevel.XO (N₀ := N₀) ρO).Opens
  x_mem_U : xpt 𝔛 bc n ∈ U
  f : (U : Scheme.{0}) ⟶ crossingScheme (((q : ℕ) : O) ^ e)
  f_over : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _
  f_fibre : ∀ y : ↥(U : Scheme.{0}),
    (CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔
      U.ι.base y = xpt 𝔛 bc n
  f_node : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = xpt 𝔛 bc n →
    (f.stalkMap y).hom.Flat ∧
      Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y)

  orient_inf : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
    U.ι.base y ∈ Set.range (𝔛.comp κ τ 0 ≫ bc).base

  orient_zero : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
    U.ι.base y ∈ Set.range (𝔛.comp κ τ 1 ≫ bc).base

  orient_inf_conv : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp κ τ 0 ≫ bc).base →
    CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal
  orient_zero_conv : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp κ τ 1 ≫ bc).base →
    CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal


end V3Glue.LevelSite

end

noncomputable section

namespace V3AsmLevel

open ModularCurve MvPolynomial MvPolynomial.CrossingQuotient

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)


structure SiteHyps : Prop where
  nodeFinite : Finite (V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO))
  hC : V3Glue.LevelSite.HasOrientedCrossingCharts 𝔛 O ρO κ (toκ.comp ρO) (bc O ρO κ toκ)
  ET : V3Glue.LevelSite.EtNbhd
  hxinj : Function.Injective (fun n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO) => V3Glue.LevelSite.xpt 𝔛 (bc O ρO κ toκ) n)
  hxcl : ∀ n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO), IsClosed ({V3Glue.LevelSite.xpt 𝔛 (bc O ρO κ toκ) n} : Set (DRLevel.XO (N₀ := N₀) ρO))
  model : V3Glue.LevelSite.ModelHyps q O

variable (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)}) (H : SiteHyps 𝔛 O ρO κ toκ)


variable (hξ : ∀ j, ξ 𝔛 O ρO κ toκ j ∈ (C 𝔛 O ρO κ toκ hϖ H).X0)


end V3AsmLevel

end
