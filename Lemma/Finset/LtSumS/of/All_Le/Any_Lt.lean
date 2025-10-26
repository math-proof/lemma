import Lemma.Finset.All_Le.of.All_Le.All_Eq_Ite
import Lemma.Finset.Sum.eq.Sum_Add_Sub.of.In_Range.All_Eq_Ite
import Lemma.Algebra.Sub.lt.Zero.of.Lt
import Lemma.Algebra.Lt.of.Eq_Add.Lt_0
import Lemma.Finset.LeSumS.of.All_Le
import Lemma.Nat.Lt.of.Le.Lt
open Algebra Finset Nat


@[main]
private lemma main
  [DecidableEq ι]
  {x y : ι → ℝ}
  {s : Finset ι}
-- given
  (h₀ : ∀ i ∈ s, x i ≤ y i)
  (h₁ : ∃ i ∈ s, x i < y i) :
-- imply
  ∑ i ∈ s, x i < ∑ i ∈ s, y i := by
-- proof
  let ⟨i', h⟩ := h₁
  let ⟨h_In, h_Lt⟩ := h
  let y' := fun i => if i = i' then x i else y i
  have h_y' : ∀ i ∈ s, y' i = if i = i' then x i else y i := by
    intro i hj
    by_cases h : i = i'
    ·
      rw [h]
    ·
      unfold y'
      simp [h]
  have := All_Le.of.All_Le.All_Eq_Ite h_In h₀ h_y'
  have h_Le := LeSumS.of.All_Le this
  have := Sum.eq.Sum_Add_Sub.of.In_Range.All_Eq_Ite h_In h_y'
  have h_Lt_0 := Sub.lt.Zero.of.Lt h_Lt
  have := Lt.of.Eq_Add.Lt_0 this h_Lt_0
  exact Lt.of.Le.Lt h_Le this


-- created on 2025-04-06
