import Mathlib
import Abbrev.ModularCurve_DRModelPackageCrossingFrame
import Structure.ModularCurve_DRResolvedModelPackageLevel
import Lemma.Scheme.DRModelPackageLevelAPI

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

noncomputable section

namespace ModularCurve

attribute [local instance] DRModelPackageLevel.neZero_mul

namespace DRLevel

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

abbrev XO.toBase {O : Type} [CommRing O] (ρO : R q →+* O) : XO (N₀ := N₀) ρO ⟶ Spec (CommRingCat.of O) :=
  pullback.snd _ _

end DRLevel

namespace DRModelPackageLevel

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  {O : Type} [CommRing O] (ρO : DRLevel.R q →+* O)
  {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)

abbrev crossingPt (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1))) : ↥(DRLevel.XO (N₀ := N₀) ρO) :=
  (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base n

abbrev baseGerm (x : ↥(DRLevel.XO (N₀ := N₀) ρO)) (o : O) : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x :=
  (DRLevel.XO (N₀ := N₀) ρO).presheaf.germ ⊤ x trivial
    ((DRLevel.XO.toBase (N₀ := N₀) ρO).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))

abbrev ξinf : ↥(DRLevel.XO (N₀ := N₀) ρO) :=
  letI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  (𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))

abbrev ξzero : ↥(DRLevel.XO (N₀ := N₀) ρO) :=
  letI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  (𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))

end DRModelPackageLevel

end ModularCurve

end
