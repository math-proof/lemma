module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.TypeStar

/-!
# Nat-indexed `GetElem` on `ℕ → α`

`f[i]` for `f : ℕ → α` and `i : ℕ` is `f i`. The validity predicate is `True`, so
`get_elem_tactic` always succeeds. This lets `x[k]` work on a sequence such as
`x : ℕ → Ω → ℝ` without going through `Fun`.

Only this Nat-indexed function type is added. A generic `GetElem (α → β) α β` would clash with
Mathlib's `P[X]` notation, which is why
`Lemma/Random/Prob/eq/Mul_ProbS/Prob/eq/Mul_MulProbS/of/CondIndep.lean` keeps its equivalent
instance `local`. The `Fun` and `Matrix` `GetElem` instances act on `Fun` / `Matrix`, not on
bare function types, so there is no overlap.
-/

@[expose] public section

/-- `f[i]` with `i : ℕ` on `f : ℕ → α` is `f i`. -/
instance instGetElemNatNat {α : Type*} : GetElem (ℕ → α) ℕ α (fun _ _ => True) where
  getElem f i _ := f i

/-- The instance above is definitional, so `simp` can also reduce a Nat-indexed read. -/
@[simp] theorem getElem_nat_apply {α : Type*} (f : ℕ → α) (i : ℕ) :
    f[i] = f i :=
  rfl
