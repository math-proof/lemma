import Mathlib
import Lemma.Definitions.Def_ExtEndgame_ChainAdm
import Lemma.Definitions.Def_GaloisRep_ComplexConjugation
import Lemma.Definitions.Def_GaloisRep_CompletionBridge
import Lemma.Definitions.Def_ClassGroup_GaloisAction

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

noncomputable instance : Fintype (extArithIndex S) :=
  inferInstanceAs (Fintype (Unit ⊕ ↥S))

def extArithLocalGroups : extArithIndex S → Type
  | Sum.inl _ => ↥archimedeanDecomposition
  | Sum.inr q => primeLocalGaloisGroup q.1

noncomputable instance : ∀ v : extArithIndex S, Group (extArithLocalGroups S v)
  | Sum.inl _ => inferInstanceAs (Group ↥archimedeanDecomposition)
  | Sum.inr q => inferInstanceAs (Group (primeLocalGaloisGroup q.1))

noncomputable def extArithLoc :
    ∀ v : extArithIndex S,
      extArithLocalGroups S v →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  | Sum.inl _ => archimedeanLoc
  | Sum.inr q => primeLocalToGlobal q.1

@[simp] lemma extArithLoc_inl (v : Unit) : extArithLoc S (Sum.inl v) = archimedeanLoc := rfl
@[simp] lemma extArithLoc_inr (q : ↥S) : extArithLoc S (Sum.inr q) = primeLocalToGlobal q.1 := rfl

def extArithDistinguished (P₂ : Set ↥S) : Set (extArithIndex S) :=
  Sum.inr '' P₂ ∪ Set.range Sum.inl

end Datum

variable (p : ℕ) [Fact p.Prime]

def pPrime : Nat.Primes := ⟨p, Fact.out⟩

@[simp] lemma pPrime_coe : ((pPrime p : Nat.Primes) : ℕ) = p := rfl

def pSet : Finset Nat.Primes := {pPrime p}

noncomputable abbrev extDualModule :
    Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  ofChar (k := ZMod p) ((cycloChar p) ^ 2)

noncomputable abbrev extDualSelmerAdm
    (pairing : ∀ v, H1 (Rep.res (extArithLoc (pSet p) v)
        (ofChar (k := ZMod p) (cycloChar p)⁻¹)) →ₗ[ZMod p]
      H1 (Rep.res (extArithLoc (pSet p) v) (extDualModule p)) →ₗ[ZMod p] (ZMod p))
    (adm' : Submodule (ZMod p) (H1 (extDualModule p))) :
    Submodule (ZMod p) (H1 (extDualModule p)) :=
  selmerAdm (extArithLoc (pSet p)) (extDualModule p)
    (dualConditions (extArithLoc (pSet p)) (ofChar (k := ZMod p) (cycloChar p)⁻¹)
      (extDualModule p) pairing
      (extConditions (extArithLoc (pSet p)) (ofChar (k := ZMod p) (cycloChar p)⁻¹)
        (extArithDistinguished (pSet p) Set.univ) (fun _ => ⊥))) adm'

end ExtCitation
