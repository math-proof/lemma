module
public import Mathlib
public import Abbrev.ModularCurve_IgusaScheme
public import Def.GaloisRep_Flat
public import Def.ModularCurve_AtkinLehnerPartial
public import Structure.AlgebraicCurve_CurveModel
public import Instance.ModularCurve_GeometricBaseChange
public import Instance.ModularCurve_ArithmeticGalois
public import Def.ModularCurve_PlaceWidthChar
public import Theorem.LaurentSeries.CoeffSemilinearAut
public import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
public import Instance.ModularCurve_IgusaScheme
public import Structure.ModularCurve_DRModelPackageLevel
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000


public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve.IgusaScheme

namespace ModularCurve

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]


namespace DRLevel

abbrev R : Type := ↥(GaloisRep.ratLocalizedAt q)

abbrev X : Scheme.{0} := IgusaScheme (N₀ * q) q
abbrev toBase : X N₀ q ⟶ Spec (CommRingCat.of (R q)) := IgusaScheme.igusaTo (N₀ * q) q

abbrev X0 : Scheme.{0} := IgusaScheme N₀ q
abbrev toBase0 : X0 N₀ q ⟶ Spec (CommRingCat.of (R q)) := IgusaScheme.igusaTo N₀ q

variable {N₀ q}

abbrev fibre {κ : Type} [CommRing κ] (toκ : R q →+* κ) : Scheme.{0} :=
  pullback (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))

abbrev fibre0 {κ : Type} [CommRing κ] (toκ : R q →+* κ) : Scheme.{0} :=
  pullback (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))


end DRLevel

open DRLevel


namespace DRModelPackageLevel

variable {N₀ q} {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)

abbrev width {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
    (n : ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1))) : ℕ :=
  placeWidthChar q N₀ ((𝔛.nodeEquiv κ toκ n : ↥(ssPlaces q N₀ κ)) : Place κ ↥(modularFunctionFieldC κ N₀))


end DRModelPackageLevel

end ModularCurve

end

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve.IgusaScheme

namespace ModularCurve

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]


namespace DRLevel


end DRLevel

open DRLevel


namespace DRModelPackageLevel

variable {N₀ q} {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)


abbrev εinf0 {κ : Type} [CommRing κ] (toκ : R q →+* κ) :=
  sectionFibre 𝔛.εinf toκ ≫ fibreMap0 𝔛.π toκ

end DRModelPackageLevel

end ModularCurve

end
