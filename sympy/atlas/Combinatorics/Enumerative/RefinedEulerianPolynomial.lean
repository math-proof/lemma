/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RefinedEulerianPolynomial.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

section
open scoped BigOperators

namespace MetaMathlibExt

private def oddC (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then
      (i.val + 1) % 2 = 1 ∧ σ i > σ ⟨i.val + 1, h⟩
    else False).card

private def evenC (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then
      (i.val + 1) % 2 = 0 ∧ σ i > σ ⟨i.val + 1, h⟩
    else False).card

private def swp (k : ℕ) (p q : ℝ) : ℝ := if k % 2 = 0 then p else q

private def swq (k : ℕ) (p q : ℝ) : ℝ := if k % 2 = 0 then q else p

private def wt {α : Type*} [LinearOrder α] : List α → ℝ → ℝ → ℝ
  | [], _, _ => 1
  | [_], _, _ => 1
  | a :: b :: t, p, q => (if b < a then p else 1) * wt (b :: t) q p

private def Fp (n : ℕ) (p q : ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), p ^ oddC n σ * q ^ evenC n σ

private def G (j : ℕ) (a b : ℝ) : ℝ :=
  if j = 0 then 1 else a * Fp j b a

private def cntO (n : ℕ) (f : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then (i.val + 1) % 2 = 1 ∧ f ⟨i.val + 1, h⟩ < f i
    else False).card

private def cntE (n : ℕ) (f : Fin n → ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    if h : i.val + 1 < n then (i.val + 1) % 2 = 0 ∧ f ⟨i.val + 1, h⟩ < f i
    else False).card

private noncomputable def Arr {α : Type*} [DecidableEq α] (S : Finset α) :
    Finset (List α) :=
  (S.toList.permutations).toFinset

private def recTerm (n k : ℕ) (p q : ℝ) : ℝ :=
  (n.choose k : ℝ) * Fp k p q * (if k = 0 then 1 else swq k p q) *
    Fp (n - k) (swp (k + 1) p q) (swq (k + 1) p q)
end MetaMathlibExt
end
