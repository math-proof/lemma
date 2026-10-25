import Mathlib
import Structure.ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Structure.ModularCurve_JZeroNeronTorsionFlag

set_option autoImplicit false

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite GaloisRep

set_option maxHeartbeats 1200000 in

structure JZeroNeronPrimaryTorsionFlag (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ) where
  n : ℕ

  G : Fin (n + 1) → Type
  [instCommRing_G : ∀ i, CommRing (G i)]
  [instHopfAlgebra_G : ∀ i, HopfAlgebra ℤ (G i)]
  [instFiniteType_G : ∀ i, Algebra.FiniteType ℤ (G i)]
  [instFlat_G : ∀ i, Module.Flat ℤ (G i)]
  π : ∀ i, C.H m →ₐ[ℤ] G i
  π_surj : ∀ i, Function.Surjective (π i)
  quot : ∀ i : Fin n, G i.succ →ₐ[ℤ] G i.castSucc
  quot_surj : ∀ i, Function.Surjective (quot i)
  quot_π : ∀ i : Fin n, (quot i).comp (π i.succ) = π i.castSucc

  F : Fin (n + 1) → Sheaf (smallFppfTopology specInt) Ab.{1}
  ι : ∀ i, F i ⟶ C.𝒥 m
  ι_mono : ∀ i, Mono (ι i)
  incl : ∀ i : Fin n, F i.castSucc ⟶ F i.succ
  incl_ι : ∀ i : Fin n, incl i ≫ ι i.succ = ι i.castSucc

  F_sectionsEquiv : ∀ (i : Fin (n + 1)) (U : specInt.Fppf),
    (F i).1.obj (op U) ≃+ Additive (WithConv (G i →ₐ[ℤ] Γ(U.left, ⊤)))

  F_sectionsCompat : ∀ (i : Fin (n + 1)) (U : specInt.Fppf) (s : (F i).1.obj (op U)) (h : C.H m),
    WithConv.ofConv (Additive.toMul (C.sectionsEquiv m U ((ι i).1.app (op U) s))) h
      = WithConv.ofConv (Additive.toMul (F_sectionsEquiv i U s)) (π i h)

  G_zero_subsingleton : Subsingleton (G 0 →ₐ[ℤ] AlgebraicClosure ℚ)
  isIso_ι_last : IsIso (ι (Fin.last n))

  genericStep : Fin (n + 1) → AddSubgroup (JZero p)
  genericStep_le_tors : ∀ i, genericStep i ≤ eisensteinPrimaryTorsionBar p q m
  genericStep_mono : Monotone genericStep
  genericStep_bot : genericStep 0 = ⊥
  genericStep_top : genericStep (Fin.last n) = eisensteinPrimaryTorsionBar p q m
  genericStep_galois : ∀ (i : Fin (n + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : JZero p), x ∈ genericStep i → σ • x ∈ genericStep i

  genericStep_pin : ∀ (i : Fin (n + 1)) (x : JZero p), x ∈ genericStep i ↔
    ∃ g : G i →ₐ[ℤ] AlgebraicClosure ℚ,
      (C.genericPoints m (WithConv.toConv (g.comp (π i))) : JZero p) = x

  kind : Fin n → JZeroFlagLayerKind

  layerAction_const : ∀ (i : Fin n), kind i = .const →
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
      x ∈ genericStep i.succ → σ • x - x ∈ genericStep i.castSucc

  layerAction_mult : ∀ (i : Fin n), kind i = .mult →
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (x : JZero p), x ∈ genericStep i.succ → σ • x - nσ • x ∈ genericStep i.castSucc
  Lff : ∀ (_ : Fin n) (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → Type
  [instCommRing_Lff : ∀ i ℓ hℓ hℓp, CommRing (Lff i ℓ hℓ hℓp)]
  [instHopfAlgebra_Lff : ∀ i ℓ hℓ hℓp, HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) (Lff i ℓ hℓ hℓp)]
  [instFinite_Lff : ∀ i ℓ hℓ hℓp, Module.Finite (GaloisRep.ratLocalizedAt ℓ) (Lff i ℓ hℓ hℓp)]
  [instFlat_Lff : ∀ i ℓ hℓ hℓp, Module.Flat (GaloisRep.ratLocalizedAt ℓ) (Lff i ℓ hℓ hℓp)]
  Lff_rank : ∀ i ℓ hℓ hℓp, Module.finrank (GaloisRep.ratLocalizedAt ℓ) (Lff i ℓ hℓ hℓp) = q

  Lff_points : ∀ (i : Fin n) ℓ hℓ hℓp,
    WithConv (Lff i ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)
      ≃ (genericStep i.succ ⧸ (genericStep i.castSucc).addSubgroupOf (genericStep i.succ))

  layerIsoConst : ∀ (i : Fin n), kind i = .const → ∀ ℓ hℓ hℓp,
    Nonempty (Lff i ℓ hℓ hℓp ≃ₐ[GaloisRep.ratLocalizedAt ℓ] (Fin q → GaloisRep.ratLocalizedAt ℓ))

  layerIsoMult : ∀ (i : Fin n), kind i = .mult → ∀ ℓ hℓ hℓp,
    Nonempty (Lff i ℓ hℓ hℓp ≃ₐ[GaloisRep.ratLocalizedAt ℓ]
      (Polynomial (GaloisRep.ratLocalizedAt ℓ)
        ⧸ Ideal.span {(Polynomial.X : Polynomial (GaloisRep.ratLocalizedAt ℓ)) ^ q - 1}))

attribute [instance] JZeroNeronPrimaryTorsionFlag.instCommRing_G JZeroNeronPrimaryTorsionFlag.instHopfAlgebra_G
  JZeroNeronPrimaryTorsionFlag.instFiniteType_G JZeroNeronPrimaryTorsionFlag.instFlat_G
  JZeroNeronPrimaryTorsionFlag.instCommRing_Lff JZeroNeronPrimaryTorsionFlag.instHopfAlgebra_Lff
  JZeroNeronPrimaryTorsionFlag.instFinite_Lff JZeroNeronPrimaryTorsionFlag.instFlat_Lff

end ModularCurve
