module
public import Mathlib
public import Instance.ExtEndgame_ProductionDatum
public import Instance.EllipticCurve_FrobeniusTrace
set_option autoImplicit false


public section

namespace ExtCitation

section RootsOfUnity

variable (q : Nat.Primes)

noncomputable abbrev toDecomp : primeLocalGaloisGroup q →* ↥((primeLocalPlace q).decompositionSubgroup ℚ) :=
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  (primeLocalToGlobal q).codRestrict _ (fun g => localGaloisToGlobal_mem_decompositionSubgroup (q : ℕ) g)

end RootsOfUnity

section Kummer

variable (p : ℕ) [Fact p.Prime] (q : Nat.Primes)

end Kummer

end ExtCitation
