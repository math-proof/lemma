import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SharpSATInIP
open SharpSATInIP
open InteractiveProofs NPCompleteness TuringMachine


namespace SharpSATInIP

/--
[acceptProb_ge_of_all_accept](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATInIP.lean)
-/
@[path]
lemma acceptProb_ge_of_all_accept
  {Q Γ : Type}
  [DecidableEq Γ]
  {V : Verifier Q Γ}
  {P : Prover Γ}
  {w : List Γ}
  {n : ℕ}
  {numRounds : ℕ}
-- given
  (h : ∀ coins : Fin n → Bool, runProtocol V P w n coins numRounds = true) :
-- imply
  V.acceptProb P w n numRounds ≥ 2 / 3 := by
-- proof
  simp only [Verifier.acceptProb, Verifier.numAccepting]
  rw [Finset.filter_eq_self.mpr (fun c _ => h c), Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat,
    div_self (pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0))]
  norm_num

end SharpSATInIP

namespace SharpSATInIP

/--
[acceptProb_le_of_all_reject](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATInIP.lean)
-/
@[path]
lemma acceptProb_le_of_all_reject
  {Q Γ : Type}
  [DecidableEq Γ]
  {V : Verifier Q Γ}
  {P : Prover Γ}
  {w : List Γ}
  {n : ℕ}
  {numRounds : ℕ}
-- given
  (h : ∀ coins : Fin n → Bool, runProtocol V P w n coins numRounds = false) :
-- imply
  V.acceptProb P w n numRounds ≤ 1 / 3 := by
-- proof
  simp only [Verifier.acceptProb, Verifier.numAccepting]
  rw [Finset.filter_eq_empty_iff.mpr
    (fun c _ => by rw [h c]; exact Bool.false_ne_true),
    Finset.card_empty, Nat.cast_zero, zero_div]
  norm_num
/--
Completeness of the sum-check protocol: if `w` encodes `⟨φ, k⟩` with
`k = #sat(φ)`, then for every coin tape the verifier accepts when run against
the honest prover. This is the easy direction of `#SAT ∈ IP`.
-/

end SharpSATInIP


-- created on 2026-10-23
