import Instance.CuspForm_HeckeLocal
import Lemma.ModularCurve.SpecializationWitness
import Def.CuspForm_LatticeHeckeFamily

noncomputable section

namespace CuspForm

variable (N : ℕ) [NeZero N]


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
