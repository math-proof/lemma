import Lemma.Definitions.Def_CuspForm_HeckeLocal
import Lemma.Definitions.Def_ModularCurve_SpecializationWitness

noncomputable section

namespace CuspForm

variable (N : ℕ) [NeZero N]

def heckeAlgebra.atPrime (ℓ : Nat.Primes) : ↥(heckeAlgebra N 2 (∅ : Set ℕ)) :=
  if h : (ℓ : ℕ) ∣ N then heckeAlgebra.U ℓ.2 h (Set.notMem_empty _) else heckeAlgebra.T ℓ.2 h (Set.notMem_empty _)

def latticeHeckeFamily : ModularCurve.CommutingHeckeFamily ↥(intLattice N 2) where
  T ℓ := latticeActionHom N ∅ (heckeAlgebra.atPrime N ℓ)
  comm q q' := (Commute.all (heckeAlgebra.atPrime N q) (heckeAlgebra.atPrime N q')).map (latticeActionHom N ∅)

theorem latticeHeckeFamily_T (ℓ : Nat.Primes) :
    (latticeHeckeFamily N).T ℓ = latticeActionHom N ∅ (heckeAlgebra.atPrime N ℓ) :=
  rfl

theorem heckeAlgebra.atPrime_of_dvd {ℓ : Nat.Primes} (h : (ℓ : ℕ) ∣ N) :
    heckeAlgebra.atPrime N ℓ = heckeAlgebra.U ℓ.2 h (Set.notMem_empty _) :=
  dif_pos h

theorem heckeAlgebra.atPrime_of_not_dvd {ℓ : Nat.Primes} (h : ¬ (ℓ : ℕ) ∣ N) :
    heckeAlgebra.atPrime N ℓ = heckeAlgebra.T ℓ.2 h (Set.notMem_empty _) :=
  dif_neg h

end CuspForm

end
