/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/KAbelianSquareFreeWord.lean -/

import Mathlib.Data.List.Basic

namespace MetaMathlibExt

/-!
# k-abelian square-free words

Source: T. Huova and A. Saarela, *Strongly k-abelian repetitions*, Journal of Integer
Sequences 16 (2013),
[`huova2.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL16/Huova/huova2.tex).
-/

/-- Number of overlapping occurrences of a nonempty factor `t` in `w`.
The empty factor is assigned count zero. -/
def wordFactorCount {α : Type*} [DecidableEq α] (w t : List α) : ℕ :=
  if t = [] then 0
  else
    match w with
    | [] => 0
    | _ :: ws => (if w.take t.length = t then 1 else 0) + wordFactorCount ws t

/-- Two nonempty words are `k`-abelian equivalent when their prefixes and suffixes of
length `k - 1` agree and every factor of length `k` occurs equally often. -/
def IsKAbelianEquivalent {α : Type*} [DecidableEq α]
    (k : ℕ) (u v : List α) : Prop :=
  1 ≤ k ∧ u ≠ [] ∧ v ≠ [] ∧
    u.take (k - 1) = v.take (k - 1) ∧
    u.drop (u.length - (k - 1)) = v.drop (v.length - (k - 1)) ∧
    ∀ t : List α, t.length = k → wordFactorCount u t = wordFactorCount v t

/-- A `k`-abelian square is a concatenation of two nonempty `k`-abelian equivalent words. -/
def IsKAbelianSquare {α : Type*} [DecidableEq α]
    (k : ℕ) (w : List α) : Prop :=
  ∃ u v : List α, w = u ++ v ∧ IsKAbelianEquivalent k u v

/-- A finite word is `k`-abelian square-free when none of its contiguous factors is a
`k`-abelian square. -/
def IsKAbelianSquareFree {α : Type*} [DecidableEq α]
    (k : ℕ) (w : List α) : Prop :=
  1 ≤ k ∧ ∀ pre factor suf : List α,
    w = pre ++ factor ++ suf → ¬ IsKAbelianSquare k factor

/-- Ternary specialization of `3`-abelian equivalence. -/
def IsThreeAbelianEquivalent (u v : List (Fin 3)) : Prop :=
  IsKAbelianEquivalent 3 u v

/-- Ternary specialization of a `3`-abelian square. -/
def IsThreeAbelianSquare (w : List (Fin 3)) : Prop :=
  IsKAbelianSquare 3 w

/-- Ternary specialization of `3`-abelian square-freeness. -/
def IsThreeAbelianSquareFree (w : List (Fin 3)) : Prop :=
  IsKAbelianSquareFree 3 w

end MetaMathlibExt
