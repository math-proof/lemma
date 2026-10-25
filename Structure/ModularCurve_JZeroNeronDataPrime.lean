import Mathlib
import Structure.ModularCurve_JZeroNeronData
import Lemma.ModularCurve.HeckeModule
import Def.ModularCurve_HeckeInputsAll
import Def.FLTPrelim_Ramification
import Def.GaloisRep_Flat

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open ValuationSubring

def inertiaInvariantPoints (p : ℕ) [NeZero p] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    AddSubgroup (JZero p) where
  carrier := {x | ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x}
  zero_mem' := fun σ _ => smul_zero σ
  add_mem' := by
    intro x y hx hy σ hσ
    rw [smul_add, hx σ hσ, hy σ hσ]
  neg_mem' := by
    intro x hx σ hσ
    rw [smul_neg, hx σ hσ]


structure JZeroNeronDataPrime (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) : Type 1 where

  toric : ℕ → AddSubgroup (JZero p)

  finPart : ℕ → AddSubgroup (JZero p)
  toric_le_finPart : ∀ m, toric m ≤ finPart m
  finPart_le_torsion : ∀ m, finPart m ≤ jZeroTorsion p m

  toric_inf : ∀ m m' : ℕ, m ∣ m' → toric m = toric m' ⊓ jZeroTorsion p m
  finPart_inf : ∀ m m' : ℕ, m ∣ m' → finPart m = finPart m' ⊓ jZeroTorsion p m

  invariants_le_finPart : ∀ m, inertiaInvariantTorsion p A m ≤ finPart m

  finPart_eq_of_coprime : ∀ m, m.Coprime p → finPart m = inertiaInvariantTorsion p A m

  toric_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero p), x ∈ toric m →
    (letI := heckeModuleBar p; t • x) ∈ toric m
  finPart_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero p), x ∈ finPart m →
    (letI := heckeModuleBar p; t • x) ∈ finPart m

  toric_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ toric m, σ • x ∈ toric m
  finPart_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ finPart m, σ • x ∈ finPart m

  inertia_toric : ∀ (m : ℕ), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (c : ℕ),
    (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) → ∀ x ∈ toric m, σ • x = c • x

  inertia_unipotent : ∀ (m : ℕ), m.Coprime p → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
    ∀ x ∈ jZeroTorsion p m, σ • x - x ∈ toric m

  toricRank : ℕ

  card_toric : ∀ m : ℕ, 0 < m → Nat.card ↥(toric m) = m ^ toricRank

  Φ : Type
  [instAddCommGroupΦ : AddCommGroup Φ]
  [instFiniteΦ : Finite Φ]
  [instModuleΦ : Module HeckeAlg Φ]

  card_Φ_coprime : (Nat.card Φ).Coprime p

  spec : ∀ m : ℕ, (↥(finPart m) →+ Φ)

  spec_ker : ∀ (m : ℕ) (x : ↥(finPart m)), spec m x = 0 ↔ (x : JZero p) ∈ toric m

  spec_range : ∀ (m : ℕ), 0 < m → (spec m).range = (Submodule.torsionBy ℤ Φ (m : ℤ)).toAddSubgroup

  spec_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : ↥(finPart m)),
    spec m ⟨(letI := heckeModuleBar p; t • (x : JZero p)), finPart_hecke m t x x.2⟩ = t • spec m x

  spec_inertia : ∀ (m : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : ↥(finPart m)) (hσx : σ • (x : JZero p) ∈ finPart m), spec m ⟨_, hσx⟩ = spec m x

  spec_compat : ∀ (m m' : ℕ) (h : m ∣ m') (x : ↥(finPart m)) (hx : (x : JZero p) ∈ finPart m'),
    spec m' ⟨x, hx⟩ = spec m x

  redComponent : ↥(inertiaInvariantPoints p A) →+ Φ

  red_spec : ∀ (m : ℕ) (x : ↥(finPart m)) (hx : (x : JZero p) ∈ inertiaInvariantPoints p A),
    redComponent ⟨x, hx⟩ = spec m x

  red_ker_iff : ∀ x : ↥(inertiaInvariantPoints p A),
    redComponent x = 0 ↔ ∃ y : ↥(inertiaInvariantPoints p A), (Nat.card Φ) • y = x

  red_hecke : ∀ (t : HeckeAlg) (x : JZero p) (hx : x ∈ inertiaInvariantPoints p A)
    (htx : (letI := heckeModuleBar p; t • x) ∈ inertiaInvariantPoints p A),
    redComponent ⟨_, htx⟩ = t • redComponent ⟨x, hx⟩

  Φ_eisenstein : HeckeInputsAll p → HeckeOperatorsCommuteBar p →
    ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ p → ∀ φ : Φ, (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • φ = 0

  toric_frob_sq : ∀ (m : ℕ), m.Coprime p → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
    ∀ x ∈ toric m, σ • σ • x = ((p : ℤ) ^ 2) • x

  toric_frob_hecke : HeckeInputsAll p → HeckeOperatorsCommuteBar p →
    ∀ (m : ℕ), m.Coprime p → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
      ∀ x ∈ toric m, σ • x = (letI := heckeModuleBar p; (((p : ℕ) : HeckeAlg) * heckeGen ⟨p, Fact.out⟩) • x)

  raynaud : p ≠ 2 → ∀ (V : AddSubgroup (JZero p)), V ≤ jZeroTorsion p p →
    ∀ (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
      [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
      [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
      (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V),
      (∀ f g, e (f * g) = e f + e g) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) → ((e g : ↥V) : JZero p) = σ • ((e f : ↥V) : JZero p)) →
      V ≤ finPart p

attribute [instance] JZeroNeronDataPrime.instAddCommGroupΦ JZeroNeronDataPrime.instFiniteΦ
  JZeroNeronDataPrime.instModuleΦ


section RationalPoints

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)


end RationalPoints

end ModularCurve

end
