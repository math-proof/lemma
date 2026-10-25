import Mathlib
import Lemma.ExtEndgame.ChainAdm
import Lemma.GaloisRep.ComplexConjugation
import Lemma.GaloisRep.CompletionBridge
import Lemma.ClassGroup.GaloisAction
import Instance.ExtEndgame_ProductionDatum
import Def.ExtEndgame_ProductionDatum
import Abbrev.ExtEndgame_ProductionDatum

set_option autoImplicit false

open CategoryTheory Module groupCohomology

namespace ExtCitation


section Datum

variable (S : Finset Nat.Primes)


@[simp] lemma extArithLoc_inl (v : Unit) : extArithLoc S (Sum.inl v) = archimedeanLoc := rfl
@[simp] lemma extArithLoc_inr (q : ↥S) : extArithLoc S (Sum.inr q) = primeLocalToGlobal q.1 := rfl

end Datum

variable (p : ℕ) [Fact p.Prime]


@[simp] lemma pPrime_coe : ((pPrime p : Nat.Primes) : ℕ) = p := rfl


end ExtCitation
