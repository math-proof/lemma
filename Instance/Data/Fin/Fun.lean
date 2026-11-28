module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.TypeStar

/-!
# Nat-indexed `GetElem` on `Fin n → α`

`f[i]` for `f : Fin n → α` and `i : ℕ` is `f ⟨i, h⟩`, with `i < n` discharged by
`get_elem_tactic` (`omega`). This removes the `⟨_, by omega⟩` boilerplate wherever a `Fin n` index
is built from Nat arithmetic, e.g. `R[((k : ℤ) - (i : ℤ)).natAbs]` for `R : Fin n → _`.

Only the Nat index is added. A generic `GetElem (α → β) α β` would clash with Mathlib's `P[X]`
notation, which is why `Lemma/Random/Prob/eq/Mul_ProbS/Prob/eq/Mul_MulProbS/of/CondIndep.lean` keeps
its equivalent instance `local`. The `Fun` and `Matrix` `GetElem` instances act on `Fun` / `Matrix`,
not on bare function types, so there is no overlap.
-/

@[expose] public section

/-- `f[i]` with `i : ℕ` on `f : Fin n → α` is `f ⟨i, i < n⟩`. -/
instance instGetElemFinNat {n : ℕ} {α : Type*} : GetElem (Fin n → α) ℕ α (fun _ i => i < n) where
  getElem f i h := f ⟨i, h⟩

/-- The instance above is definitional, so `simp` can also reduce a Nat-indexed read. -/
@[simp] theorem getElem_fin_apply {n : ℕ} {α : Type*} (f : Fin n → α) (i : ℕ) (h : i < n) :
    f[i] = f ⟨i, h⟩ :=
  rfl

/-- `f i` with `i : Fin n` equals the `GetElem` read `f[i]`; the `Fin n` index is coerced to
`ℕ` and discharged by `get_elem_tactic`.

Deliberately *not* a `@[simp]` lemma. With `getElem_fin_apply` in the default simp set it forms
the cycle `f i → f[i] → f ⟨(i:ℕ), _⟩ → …` which overflows `maxRecDepth`, and even alone an
unanchored `simp only [getElem_fin]` (LHS `?f ?i` is all metavariables) can diverge. Invoke it
with the function anchored, e.g. `simp only [getElem_fin f]`, or `rw [getElem_fin f i]`. -/
theorem getElem_fin {n : ℕ} {α : Type*} (f : Fin n → α) (i : Fin n) :
    f i = f[i] :=
  rfl
