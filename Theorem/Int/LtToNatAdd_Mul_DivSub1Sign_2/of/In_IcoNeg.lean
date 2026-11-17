module

public import Def.Data.List.Slice
public import Theorem.Int.InAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
public import Theorem.Int.EqToNat.of.Ge_0

public section

open Int


public theorem Int.LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
  {i : ℤ}
  {n : ℕ}
-- given
  (h : i ∈ Ico (-n : ℤ) n) :
-- imply
  (Slice.Add_Mul_DivSub1Sign_2 n i).toNat < n := by
-- proof
  have h := InAdd_Mul_DivSub1Sign_2.of.In_IcoNeg h
  let ⟨h_le, h_lt⟩ := h
  have := EqToNat.of.Ge_0 h_le
  simp_all


-- created on 2025-06-26
