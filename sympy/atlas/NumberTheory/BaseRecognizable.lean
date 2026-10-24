/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring

/-!
# Base-`k` recognizable sets of natural numbers

A finite-automaton interface for subsets of `ℕ` recognizable in base `k`, shared by Cobham's
theorem on base dependence and Cobham's gap theorem.
-/

namespace MetaMathlibExt

/-- The value of a base-`k` digit word, with its most significant digit first. -/
def baseWordValue {k : ℕ} (w : List (Fin k)) : ℕ :=
  w.foldl (fun value digit ↦ value * k + digit.val) 0

/-- A canonical base expansion is empty for zero and otherwise has no leading zero. -/
def IsCanonicalBaseWord {k : ℕ} : List (Fin k) → Prop
  | [] => True
  | digit :: _ => digit.val ≠ 0

/-- A subset of `ℕ` is recognizable in base `k` when a finite deterministic
automaton accepts exactly its canonical base-`k` expansions. -/
def IsBaseRecognizable (k : ℕ) (S : Set ℕ) : Prop :=
  2 ≤ k ∧
    ∃ numStates : ℕ, 0 < numStates ∧
      ∃ init : Fin numStates,
        ∃ transition : Fin numStates → Fin k → Fin numStates,
          ∃ accept : Fin numStates → Bool,
            ∀ w : List (Fin k),
              (accept (w.foldl transition init) = true ↔
                IsCanonicalBaseWord w ∧ baseWordValue w ∈ S)

/-- The canonical base-`k` expansion of `n`, most significant digit first. -/
def baseDigits {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : List (Fin k) :=
  (Nat.digits k n).reverse.map fun d ↦ ⟨d % k, Nat.mod_lt _ (by omega)⟩
end MetaMathlibExt
