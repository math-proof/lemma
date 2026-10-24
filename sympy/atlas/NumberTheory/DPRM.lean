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

open scoped Dioph Vector3 Nat Function

namespace MathlibExt.NumberTheory.DPRMWanted

/-- Natural-number polynomial expressions in variables `γ`. -/
private inductive dpNatPoly {γ : Type} : ((γ → ℕ) → ℕ) → Prop
  | var (i : γ) : dpNatPoly (fun v => v i)
  | const (n : ℕ) : dpNatPoly (fun _ => n)
  | add {F₁ F₂ : (γ → ℕ) → ℕ} :
      dpNatPoly F₁ → dpNatPoly F₂ → dpNatPoly (fun v => F₁ v + F₂ v)
  | mul {F₁ F₂ : (γ → ℕ) → ℕ} :
      dpNatPoly F₁ → dpNatPoly F₂ → dpNatPoly (fun v => F₁ v * F₂ v)

/-- Modulus for the product trick: `N = t * (1 + x * t) ^ x + 1`. -/
private def dpProdN (x t : ℕ) : ℕ := t * (1 + x * t) ^ x + 1

/-- The product `Π_{j<x} (1 + (j+1) * t)`. -/
private def dpProdP (x t : ℕ) : ℕ :=
  ∏ j ∈ Finset.range x, (1 + (j + 1) * t)

/-- Backward direction: a β-coded sequence runs inside the recursion. -/
private theorem dp_prec_bwd (f g : ℕ →. ℕ) (a c : ℕ)
    (h0 : Nat.beta c 0 ∈ f a) :
    ∀ (k : ℕ),
      (∀ j, j < k →
        Nat.beta c (j + 1) ∈ g (Nat.pair a (Nat.pair j (Nat.beta c j)))) →
      Nat.beta c k ∈ Nat.rec (motive := fun _ => Part ℕ) (f a)
        (fun j (IH : Part ℕ) => do
          let i ← IH; g (Nat.pair a (Nat.pair j i))) k := by
  intro k
  induction k with
  | zero =>
    intro _
    exact h0
  | succ k ih =>
    intro hall
    exact Part.mem_bind_iff.mpr
      ⟨Nat.beta c k, ih (fun j hj => hall j (by omega)),
        hall k (Nat.lt_succ_self k)⟩

/-- The bound `Q(v, u)` for the bounded-quantifier argument. -/
private def dpBQ_Q {α : Type} (m : ℕ) (F G : (Option (Option α) ⊕ Fin m → ℕ) → ℕ)
    (v : Option α → ℕ) (u : ℕ) : ℕ :=
  F (Sum.elim (Option.elim' (v none) v) (fun _ => u)) +
    G (Sum.elim (Option.elim' (v none) v) (fun _ => u)) + v none + u + 1

/-- Variable map for the `Q` bound in the bounded-quantifier matrix. -/
private def dpBQ_σQ {α : Type} (m : ℕ) :
    (Option (Option α) ⊕ Fin m) → ((Option α) ⊕ (Fin 3 ⊕ Fin m)) :=
  fun i => match i with
  | Sum.inl none => Sum.inl none
  | Sum.inl (some o) => Sum.inl o
  | Sum.inr _ => Sum.inr (Sum.inl 0)

/-- Variable map for the polynomial in the bounded-quantifier matrix. -/
private def dpBQ_σP {α : Type} (m : ℕ) :
    (Option (Option α) ⊕ Fin m) → ((Option α) ⊕ (Fin 3 ⊕ Fin m)) :=
  fun i => match i with
  | Sum.inl none => Sum.inr (Sum.inl 2)
  | Sum.inl (some o) => Sum.inl o
  | Sum.inr j => Sum.inr (Sum.inr j)
end MathlibExt.NumberTheory.DPRMWanted
namespace MathlibExt.NumberTheory.DPRMWanted
end MathlibExt.NumberTheory.DPRMWanted
