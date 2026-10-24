import Mathlib
import Lemma.Definitions.Def_ModularCurve_JZeroNeronAtPDataSameIdeal

set_option autoImplicit false

noncomputable section

namespace ModularCurve

structure JZeroNeronAtPDataCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) : Type 1 where

  toric : ℕ → AddSubgroup (JZero (N * q))

  fin : ℕ → AddSubgroup (JZero (N * q))

  finPart : ℕ → AddSubgroup (JZero (N * q))
  toric_le_fin : ∀ m, toric m ≤ fin m
  fin_le_finPart : ∀ m, fin m ≤ finPart m
  finPart_le_torsion : ∀ m, finPart m ≤ jZeroTorsion (N * q) m
  finPart_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero (N * q)), x ∈ finPart m →
    (letI := heckeModuleBar (N * q); t • x) ∈ finPart m
  finPart_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ finPart m, σ • x ∈ finPart m

  inertia_toric : ∀ (m : ℕ), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (c : ℕ),
    (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) → ∀ x ∈ toric m, σ • x = c • x

  Φ : Type
  [instAddCommGroupΦ : AddCommGroup Φ]
  [instFiniteΦ : Finite Φ]
  [instModuleΦ : Module HeckeAlg Φ]

  spec : ∀ m : ℕ, (↥(finPart m) →+ Φ)

  spec_ker : ∀ (m : ℕ) (x : ↥(finPart m)), spec m x = 0 ↔ (x : JZero (N * q)) ∈ fin m

  spec_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : ↥(finPart m)),
    spec m ⟨(letI := heckeModuleBar (N * q); t • (x : JZero (N * q))), finPart_hecke m t x x.2⟩ = t • spec m x

  Φ_eisenstein : HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q → ∀ φ : Φ, (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • φ = 0

  raynaud : q ≠ 2 → ∀ (V : AddSubgroup (JZero (N * q))), V ≤ jZeroTorsion (N * q) q →
    ∀ (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
      [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
      [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
      (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥V),
      (∀ f g, e (f * g) = e f + e g) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) → ((e g : ↥V) : JZero (N * q)) = σ • ((e f : ↥V) : JZero (N * q))) →
      V ≤ finPart q

  fin_heckeTorsion_detects_lowerLevel :
    HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    HeckeInputsAll N → HeckeOperatorsCommuteBar N →
      ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ((q : ℕ) : HeckeAlg) ∈ 𝔪 →
        ∀ x ∈ fin q, (letI := heckeModuleBar (N * q); x ∈ heckeTorsion (JZero (N * q)) 𝔪) →
          x ∉ toric q →
            (letI := heckeModuleBar N; HasLowerLevelTorsion (primesOf (N * q)) 𝔪 (JZero N))

  fin_heckeTorsion_detects_lowerLevel_sameIdeal :
    HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    HeckeInputsAll N → HeckeOperatorsCommuteBar N →
      ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ((q : ℕ) : HeckeAlg) ∈ 𝔪 → heckeGen ⟨q, Fact.out⟩ ∉ 𝔪 →
        ∀ x ∈ fin q, (letI := heckeModuleBar (N * q); x ∈ heckeTorsion (JZero (N * q)) 𝔪) →
          x ∉ toric q →
            (letI := heckeModuleBar N; heckeTorsion (JZero N) 𝔪 ≠ ⊥)

attribute [instance] JZeroNeronAtPDataCore.instAddCommGroupΦ JZeroNeronAtPDataCore.instFiniteΦ
  JZeroNeronAtPDataCore.instModuleΦ

def HasJZeroNeronAtPDataCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataCore N q hqN A hA)

def JZeroNeronAtPDataSameIdeal.toCore {N q : ℕ} [NeZero N] [Fact q.Prime] {hqN : ¬ q ∣ N}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime q}
    (D : JZeroNeronAtPDataSameIdeal N q hqN A hA) : JZeroNeronAtPDataCore N q hqN A hA where
  toric := D.toric
  fin := D.fin
  finPart := D.finPart
  toric_le_fin := D.toric_le_fin
  fin_le_finPart := D.fin_le_finPart
  finPart_le_torsion := D.finPart_le_torsion
  finPart_hecke := D.finPart_hecke
  finPart_dec := D.finPart_dec
  inertia_toric := D.inertia_toric
  Φ := D.Φ
  spec := D.spec
  spec_ker := D.spec_ker
  spec_hecke := D.spec_hecke
  Φ_eisenstein := D.Φ_eisenstein
  raynaud := D.raynaud
  fin_heckeTorsion_detects_lowerLevel := D.fin_heckeTorsion_detects_lowerLevel
  fin_heckeTorsion_detects_lowerLevel_sameIdeal := D.fin_heckeTorsion_detects_lowerLevel_sameIdeal

end ModularCurve

end
