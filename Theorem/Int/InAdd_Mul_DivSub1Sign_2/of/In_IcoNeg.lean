module

public import Def.Data.List.Slice
public import Theorem.Data.Set.Sets
public import Theorem.Int.DivSub1Sign_2.eq.Zero.of.Ge_0
public import Theorem.Int.DivSub1Sign_2.eq.One.of.Lt_0
public import Theorem.Int.Le0Sub.is.Ge

public section

open Int


public theorem Int.InAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
  {i : ℤ}
  {n : ℕ}
-- given
  (h : i ∈ Ico (-n : ℤ) n) :
-- imply
  Slice.Add_Mul_DivSub1Sign_2 n i ∈ Ico (0 : ℤ) n := by
-- proof
  let ⟨h_le, h_lt⟩ := h
  constructor <;>
  ·
    unfold Slice.Add_Mul_DivSub1Sign_2
    if h_i : i ≥ 0 then
      have := DivSub1Sign_2.eq.Zero.of.Ge_0 h_i
      simp_all
    else
      simp at h_i
      have := DivSub1Sign_2.eq.One.of.Lt_0 h_i
      have := Le0Sub.of.Ge h_le
      simp_all


-- created on 2025-06-26
