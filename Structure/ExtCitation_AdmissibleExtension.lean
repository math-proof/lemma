import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Def.FLTPrelim_Ramification

set_option autoImplicit false

theorem IsAlgClosed.card_rootsOfUnity_eq (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (n : ℕ) [NeZero n] : Nat.card (rootsOfUnity n K) = n :=
  haveI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  HasEnoughRootsOfUnity.natCard_rootsOfUnity K n

namespace ExtCitation

open ValuationSubring

variable (p : ℕ) [Fact p.Prime]

theorem card_rootsOfUnity_eq_self :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    Nat.card (rootsOfUnity p (AlgebraicClosure ℚ)) = p :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) p

noncomputable def cycloExp (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ℕ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ((modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) : (ZMod p)ˣ) : ZMod p).val

variable (V : Type) [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]

structure IsAdmissibleExtension (C : Submodule (ZMod p) V) : Prop where
  stable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ C, σ • x ∈ C
  fixed_sub : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ C, σ • x = x
  cyclo_quot : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x : V,
    σ • x - (cycloExp p σ : ZMod p) • x ∈ C
  card_sub : Nat.card C = p
  card_total : Nat.card V = p ^ 2
  unramified_outside : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : V, σ • x = x
  locally_split : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∃ C' : Submodule (ZMod p) V,
      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ C', σ • x ∈ C') ∧ IsCompl C C'

variable {p V} in


end ExtCitation
