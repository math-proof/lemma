import Mathlib
import Def.ModularCurve_JZeroToricTorsion
import Lemma.ModularCurve.HeckeModule
import Def.FLTPrelim_Ramification
import Def.GaloisRep_Flat

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite

structure JZeroTorsionHopfOrder (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (V : ℕ → AddSubgroup (JZero p)) where
  H : ℕ → Type
  [instCommRing_H : ∀ m, CommRing (H m)]
  [instHopfAlgebra_H : ∀ m, HopfAlgebra ℤ (H m)]
  [instFiniteType_H : ∀ m, Algebra.FiniteType ℤ (H m)]
  [instFlat_H : ∀ m, Module.Flat ℤ (H m)]
  ff_finite : ∀ (m ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
    Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) (H m))
  genericPoints : ∀ m, WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ) ≃ ↥(V m)

  genericConv : ∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    genericPoints m (f * g) = genericPoints m f + genericPoints m g

  genericGalois : ∀ m, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ f g : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    (∀ h : H m, g h = σ (f h)) →
    ((genericPoints m g : ↥(V m)) : JZero p)
      = σ • ((genericPoints m f : ↥(V m)) : JZero p)
  pFibrePoints : ∀ m, WithConv (H m →ₐ[ℤ] ↥A) ≃ ↥(jZeroToricTorsion p A (q ^ m) ⊓ V m)

  pFibreConv : ∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] ↥A),
    pFibrePoints m (f * g) = pFibrePoints m f + pFibrePoints m g

  pFibreGenericCompat : ∀ m, ∀ φ : WithConv (H m →ₐ[ℤ] ↥A),
    ∀ ψ : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    (∀ h : H m, ψ h = A.subtype (φ h)) →
    ((pFibrePoints m φ : ↥(jZeroToricTorsion p A (q ^ m) ⊓ V m)) : JZero p)
      = ((genericPoints m ψ : ↥(V m)) : JZero p)

  pointsComm : ∀ (m : ℕ) (T : Type) [CommRing T], ∀ f g : WithConv (H m →ₐ[ℤ] T), f * g = g * f

  levelMap : ∀ m, H (m + 1) →ₐc[ℤ] H m
  levelMap_surjective : ∀ m, Function.Surjective (levelMap m)
  levelMap_genericPoints : ∀ (m : ℕ) (hle : V m ≤ V (m + 1)) (φ : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ)),
    ((genericPoints (m + 1)
        (WithConv.toConv ((WithConv.ofConv φ).comp (levelMap m : H (m + 1) →ₐ[ℤ] H m))) : ↥(V (m + 1))) : JZero p)
      = ((genericPoints m φ : ↥(V m)) : JZero p)

attribute [instance] JZeroTorsionHopfOrder.instCommRing_H
  JZeroTorsionHopfOrder.instHopfAlgebra_H JZeroTorsionHopfOrder.instFiniteType_H
  JZeroTorsionHopfOrder.instFlat_H

end ModularCurve

end
