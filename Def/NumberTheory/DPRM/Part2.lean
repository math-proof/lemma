/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DPRM.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Computability.RE
public import Mathlib.NumberTheory.Dioph
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Logic.Godel.GodelBetaFunction
public import Mathlib.Tactic
public import Theorem.NumberTheory.DPRM

@[expose] public section

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
