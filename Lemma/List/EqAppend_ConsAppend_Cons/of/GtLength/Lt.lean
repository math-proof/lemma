import Lemma.List.TakeSwap.eq.Take.of.Lt
import Lemma.List.SliceSwap.eq.Slice.of.Lt
import Lemma.List.DropSwap.eq.Drop.of.Lt
import Lemma.List.EqAppendTake__Drop
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.Nat.LeAdd_1.of.Lt
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
  {i j : ℕ}
-- given
  (h₀ : i < j)
  (h₁ : s.length > j) :
-- imply
  let s' := s.swap i j
  s'.take i ++ s[i] :: (s'.slice (i + 1) j ++ s[j] :: s'.drop (j + 1)) = s := by
-- proof
  intro s'
  rw [TakeSwap.eq.Take.of.Lt h₀]
  rw [SliceSwap.eq.Slice.of.Lt h₀]
  rw [DropSwap.eq.Drop.of.Lt h₀]
  simp
  unfold List.slice
  unfold List.array_slice
  simp
  have h_eq := EqAppendTake__Drop (s.drop (i + 1)) (j - (i + 1))
  simp only [DropDrop.eq.Drop_Add] at h_eq
  simp only [EqAdd_Sub.of.Ge (by apply LeAdd_1.of.Lt h₀)] at h_eq
  rw [h_eq]
  simp


-- created on 2025-05-17
