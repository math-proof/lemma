module

public import Theorem.List.LengthFlattenTake.eq.Mul.of.GeLength.All_Eq
public import Theorem.Nat.Le.of.Lt
public import Theorem.List.AppendFlattenS.eq.Flatten
public import Theorem.List.LengthAppend.eq.AddLengthS
public import Theorem.Nat.LtAddS.is.Lt
public import Theorem.List.FlattenDrop.eq.Append_FlattenDrop.of.GtLength
public import Theorem.List.GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength
public import Theorem.List.AddMul.lt.LengthFlatten.of.Lt.GtLength.All_EqLength

public section

open List Nat


public theorem List.GetFlatten_AddMul.eq.Get.of.Lt.GtLength.All_EqLength
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
  rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength (by linarith)]
  simp_all [FlattenDrop.eq.Append_FlattenDrop.of.GtLength h₁]


-- created on 2025-06-13
-- updated on 2025-06-28
