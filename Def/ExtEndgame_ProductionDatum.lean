import Mathlib
import Def.GaloisRep_ComplexConjugation
import Lemma.PadicAlgCl.CompletionBridge

set_option autoImplicit false

open CategoryTheory Module groupCohomology

namespace ExtCitation

def primeLocalGaloisGroup (q : Nat.Primes) : Type :=
  letI : Fact (q : ℕ).Prime := ⟨q.2⟩
  PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ)

noncomputable instance (q : Nat.Primes) : Group (primeLocalGaloisGroup q) :=
  letI : Fact (q : ℕ).Prime := ⟨q.2⟩
  inferInstanceAs (Group (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ)))

noncomputable def primeLocalPlace (q : Nat.Primes) : ValuationSubring (AlgebraicClosure ℚ) :=
  letI : Fact (q : ℕ).Prime := ⟨q.2⟩
  padicPlace (q : ℕ)

noncomputable def primeLocalToGlobal (q : Nat.Primes) :
    primeLocalGaloisGroup q →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  letI : Fact (q : ℕ).Prime := ⟨q.2⟩
  localGaloisToGlobal (q : ℕ)

section Datum

variable (S : Finset Nat.Primes)

def extArithIndex : Type := Unit ⊕ ↥S

def extArithLocalGroups : extArithIndex S → Type
  | Sum.inl _ => ↥archimedeanDecomposition
  | Sum.inr q => primeLocalGaloisGroup q.1

noncomputable instance : Fintype (extArithIndex S) :=
  inferInstanceAs (Fintype (Unit ⊕ ↥S))

noncomputable instance : ∀ v : extArithIndex S, Group (extArithLocalGroups S v)
  | Sum.inl _ => inferInstanceAs (Group ↥archimedeanDecomposition)
  | Sum.inr q => inferInstanceAs (Group (primeLocalGaloisGroup q.1))

noncomputable def extArithLoc :
    ∀ v : extArithIndex S,
      extArithLocalGroups S v →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  | Sum.inl _ => archimedeanLoc
  | Sum.inr q => primeLocalToGlobal q.1


def extArithDistinguished (P₂ : Set ↥S) : Set (extArithIndex S) :=
  Sum.inr '' P₂ ∪ Set.range Sum.inl

end Datum

variable (p : ℕ) [Fact p.Prime]

def pPrime : Nat.Primes := ⟨p, Fact.out⟩


def pSet : Finset Nat.Primes := {pPrime p}

end ExtCitation
