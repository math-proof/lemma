import Instance.CuspForm_HeckeLocal
import Instance.ModularCurve_SpecializationWitness

noncomputable section

namespace CuspForm

variable (N : ℕ) [NeZero N]

def heckeAlgebra.atPrime (ℓ : Nat.Primes) : ↥(heckeAlgebra N 2 (∅ : Set ℕ)) :=
  if h : (ℓ : ℕ) ∣ N then heckeAlgebra.U ℓ.2 h (Set.notMem_empty _) else heckeAlgebra.T ℓ.2 h (Set.notMem_empty _)

def latticeHeckeFamily : ModularCurve.CommutingHeckeFamily ↥(intLattice N 2) where
  T ℓ := latticeActionHom N ∅ (heckeAlgebra.atPrime N ℓ)
  comm q q' := (Commute.all (heckeAlgebra.atPrime N q) (heckeAlgebra.atPrime N q')).map (latticeActionHom N ∅)

end CuspForm

end
