import Mathlib
import sympy.Basic
import sympy.atlas.Computability.RiceTheorem
open MetaMathlibExt


/--
[acceptableNumbering_fixed_point](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Computability/RiceTheorem.lean)
-/
@[path]
private lemma acceptableNumbering_fixed_point_eq
  {φ : ℕ → ℕ →. ℕ}
  {h : ℕ → ℕ}
-- given
  (huniv : Nat.Partrec (fun p => φ (Nat.unpair p).1 (Nat.unpair p).2))
  (hidx : ∀ f : ℕ →. ℕ, Nat.Partrec f → ∃ e, ∀ n, φ e n = f n)
  (hsmn : ∀ g : ℕ → ℕ →. ℕ, Nat.Partrec (fun p => g (Nat.unpair p).1 (Nat.unpair p).2) → ∃ s : ℕ → ℕ, Nat.Partrec (fun n => Part.some (s n)) ∧ ∀ e n, φ (s e) n = g e n)
  (hh : Computable h) :
-- imply
  ∃ e, ∀ n, φ e n = φ (h e) n := by
-- proof
  apply MetaMathlibExt.acceptableNumbering_fixed_point φ huniv hidx hsmn hh

/--
[rice_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Computability/RiceTheorem.lean)
-/
@[path]
private lemma rice_theorem_eq
  :
-- imply
  ∀ (φ : ℕ → ℕ →. ℕ),
    (∀ e, Nat.Partrec (φ e)) →
    Nat.Partrec (fun p => φ (Nat.unpair p).1 (Nat.unpair p).2) →
    (∀ f : ℕ →. ℕ, Nat.Partrec f → ∃ e, ∀ n, φ e n = f n) →
    (∀ g : ℕ → ℕ →. ℕ,
    Nat.Partrec (fun p => g (Nat.unpair p).1 (Nat.unpair p).2) →
    ∃ s : ℕ → ℕ, Nat.Partrec (fun n => Part.some (s n)) ∧
    ∀ e n, φ (s e) n = g e n) →
    ∀ (C : Set ℕ),
    (∀ a b, (∀ n, φ a n = φ b n) → (a ∈ C ↔ b ∈ C)) →
    (∃ a, a ∈ C) → (∃ b, b ∉ C) →
    ¬ ∃ dec : ℕ → ℕ, Nat.Partrec (fun n => Part.some (dec n)) ∧
    ∀ e, (e ∈ C ↔ dec e = 1) ∧ (e ∉ C ↔ dec e = 0) := by
-- proof
  apply MetaMathlibExt.rice_theorem


-- created on 2026-10-20
