import Mathlib
import Structure.ExtEndgame_ChainAdm
import Instance.GaloisRep_ComplexConjugation
import Instance.GaloisRep_CompletionBridge
import Lemma.ClassGroup.GaloisAction

set_option autoImplicit false

open CategoryTheory Module groupCohomology

namespace ExtCitation


section Datum

variable (S : Finset Nat.Primes)


end Datum

variable (p : ℕ) [Fact p.Prime]


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
