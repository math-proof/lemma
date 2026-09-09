import Lemma.Finset.Insert_Range.eq.Range
open Finset


@[main]
private lemma main
  {n : ℕ}
  {p : ℕ → ℕ}
-- given
  (h₀ : p n = n)
  (h₁ : (range (n + 1)).image p = range (n + 1)) :
-- imply
  (range n).image p = range n := by
-- proof
  have himg : (range (n + 1)).image p = insert n ((range n).image p) := by
    rw [Insert_Range.eq.Range, image_insert, h₀]
  have heq : insert n ((range n).image p) = insert n (range n) := by
    rw [← himg, h₁, Insert_Range.eq.Range]
  have hn : n ∉ (range n).image p := by
    intro hn
    obtain ⟨i, hi, hpi⟩ := mem_image.mp hn
    have hinj := injOn_of_card_image_eq (by rw [h₁])
    have : i = n :=
      hinj
        (mem_range.mpr (Nat.lt_succ_of_lt (mem_range.mp hi)))
        (self_mem_range_succ n)
        (hpi.trans h₀.symm)
    exact Nat.ne_of_lt (mem_range.mp hi) this
  calc
    _ = (insert n ((range n).image p)).erase n := (erase_insert hn).symm
    _ = (insert n (range n)).erase n := by rw [heq]
    _ = range n := erase_insert notMem_range_self


-- created on 2020-07-08
-- updated on 2026-09-09
