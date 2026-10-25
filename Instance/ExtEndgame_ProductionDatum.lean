-- Carved from Lemma/Definitions/Def_ExtEndgame_ProductionDatum.lean: instance decls only.
import Mathlib
import Lemma.ExtEndgame.ChainAdm
import Instance.GaloisRep_ComplexConjugation
import Instance.GaloisRep_CompletionBridge
import Lemma.ClassGroup.GaloisAction

set_option autoImplicit false

open CategoryTheory Module groupCohomology

namespace ExtCitation

noncomputable instance (q : Nat.Primes) : Group (primeLocalGaloisGroup q) :=
  letI : Fact (q : ℕ).Prime := ⟨q.2⟩
  inferInstanceAs (Group (PadicAlgCl (q : ℕ) ≃ₐ[ℚ_[(q : ℕ)]] PadicAlgCl (q : ℕ)))

section Datum

variable (S : Finset Nat.Primes)

noncomputable instance : Fintype (extArithIndex S) :=
  inferInstanceAs (Fintype (Unit ⊕ ↥S))

noncomputable instance : ∀ v : extArithIndex S, Group (extArithLocalGroups S v)
  | Sum.inl _ => inferInstanceAs (Group ↥archimedeanDecomposition)
  | Sum.inr q => inferInstanceAs (Group (primeLocalGaloisGroup q.1))

end Datum

variable (p : ℕ) [Fact p.Prime]

end ExtCitation
