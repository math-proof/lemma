import sympy.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Lemma.Set.InMul.of.In.Gt_0
import Lemma.Finset.Cons.eq.Union
open Finset


@[main]
private lemma main
  {A : Set ℕ}
  [ClosedUnderAdd A]
  {s : Finset ℕ}
  {f : ℕ → ℕ}
-- given
  (hs : s.Nonempty) :
-- imply
  (∀ i ∈ s, i ∈ A ∧ 0 < f i) → (s.sum fun i => i * f i) ∈ A := by
-- proof
  have hA := (inferInstance : ClosedUnderAdd A).closed_under_add
  refine Nonempty.cons_induction (singleton := ?singleton) (cons := ?cons) hs
  case singleton =>
    intro a h
    obtain ⟨ha, hfa⟩ := h a (by simp)
    simp
    rw [mul_comm]
    exact Set.InMul.of.In.Gt_0 (n := f a) (x := a) hfa ha
  case cons =>
    intro a s hnotmem hs hbase hnew
    have hcons := Finset.Cons.eq.Union hnotmem
    rw [hcons]
    rw [hcons] at hnew
    rw [sum_union (h := by simp [hnotmem])]
    simp
    apply hA
    · have : ∀ i ∈ s, i ∈ A ∧ 0 < f i := by
        intro i hi
        exact hnew i (by simp [hi])
      exact hbase this
    · obtain ⟨ha, hf⟩ := hnew a (by simp)
      rw [mul_comm]
      exact Set.InMul.of.In.Gt_0 (n := f a) (x := a) hf ha


-- created on 2026-09-18
