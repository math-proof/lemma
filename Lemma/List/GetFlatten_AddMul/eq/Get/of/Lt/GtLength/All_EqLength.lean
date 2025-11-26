import Lemma.List.LengthFlattenTake.eq.Mul.of.GeLength.All_Eq
import Lemma.Nat.Le.of.Lt
import Lemma.List.AppendFlattenS.eq.Flatten
import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.Nat.LtAddS.is.Lt
import Lemma.List.FlattenDrop.eq.Append_FlattenDrop.of.GtLength
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.List.AddMul.lt.LengthFlatten.of.Lt.GtLength.All_EqLength
open List Nat


@[main]
private lemma main
  {i j n : ℕ}
  {s : List (List α)}
-- given
  (h₀ : ∀ l ∈ s, l.length = n)
  (h₁ : s.length > i)
  (h₂ : j < n) :
-- imply
  have : j < s[i].length := by
    specialize h₀ s[i]
    simp at h₀
    simp_all
  have := AddMul.lt.LengthFlatten.of.Lt.GtLength.All_EqLength h₀ h₁ h₂
  s.flatten[i * n + j] = s[i][j] := by
-- proof
  intro h₂ h₃
  have := AppendFlattenS.eq.Flatten s i
  rw [← this] at h₃
  simp [← this]
  rw [LengthAppend.eq.AddLengthS] at h₃
  have := Le.of.Lt h₁
  rw [LengthFlattenTake.eq.Mul.of.GeLength.All_Eq h₀ this] at h₃
  have h₃ := Lt.of.LtAddS.left h₃
  have := LengthFlattenTake.eq.Mul.of.GeLength.All_Eq (by assumption) (by assumption)
  rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength (by linarith)]
  simp_all [FlattenDrop.eq.Append_FlattenDrop.of.GtLength h₁]


-- created on 2025-06-13
-- updated on 2025-06-28
