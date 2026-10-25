/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DPRM.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Computability.RE
import Mathlib.NumberTheory.Dioph
import Mathlib.Computability.Primrec.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Logic.Godel.GodelBetaFunction
import Mathlib.Tactic
import Theorem.NumberTheory.DPRM
open scoped Dioph Vector3 Nat Function


namespace MathlibExt.NumberTheory.DPRMWanted

/-- The bound `Q(v, u)` for the bounded-quantifier argument. -/
def dpBQ_Q {α : Type} (m : ℕ) (F G : (Option (Option α) ⊕ Fin m → ℕ) → ℕ)
    (v : Option α → ℕ) (u : ℕ) : ℕ :=
  F (Sum.elim (Option.elim' (v none) v) (fun _ => u)) +
    G (Sum.elim (Option.elim' (v none) v) (fun _ => u)) + v none + u + 1

/-- Variable map for the `Q` bound in the bounded-quantifier matrix. -/
def dpBQ_σQ {α : Type} (m : ℕ) :
    (Option (Option α) ⊕ Fin m) → ((Option α) ⊕ (Fin 3 ⊕ Fin m)) :=
  fun i => match i with
  | Sum.inl none => Sum.inl none
  | Sum.inl (some o) => Sum.inl o
  | Sum.inr _ => Sum.inr (Sum.inl 0)

/-- Variable map for the polynomial in the bounded-quantifier matrix. -/
def dpBQ_σP {α : Type} (m : ℕ) :
    (Option (Option α) ⊕ Fin m) → ((Option α) ⊕ (Fin 3 ⊕ Fin m)) :=
  fun i => match i with
  | Sum.inl none => Sum.inr (Sum.inl 2)
  | Sum.inl (some o) => Sum.inl o
  | Sum.inr j => Sum.inr (Sum.inr j)

end MathlibExt.NumberTheory.DPRMWanted
