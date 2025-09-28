import Lemma.Algebra.EqSumS.of.All_Eq
import Lemma.Set.Lt.of.In_Range
import Lemma.Algebra.SubAdd.eq.Add_Sub
import Lemma.Algebra.Add
import Lemma.Algebra.AddSub.eq.SubAdd
import Lemma.Algebra.EqAddS.is.Eq
open Algebra Set


@[main]
private lemma main
  {n i' : ℕ}
  {x y y' : ℕ → ℝ}
-- given
  (h₀ : i' ∈ range n)
  (h₁ : ∀ i ∈ range n, y' i = if i = i' then x i else y i) :
-- imply
  ∑ i ∈ range n, y' i = (∑ i ∈ range n, y i) + (x i' - y i') := by
-- proof
  have := EqSumS.of.All_Eq h₁
  rw [Finset.sum_ite] at this
  simp [Lt.of.In_Range h₀] at this
  rw [this]
  rw [Add.comm]
  rw [Add_Sub.eq.SubAdd]
  rw [SubAdd.eq.AddSub]
  apply EqAddS.of.Eq (x i')
  rw [Finset.sum_filter]
  let y'' := fun i => if i = i' then y i else y i
  have h_y'' : ∀ i ∈ range n, y'' i = if i = i' then y i else y i := by
    intro i hi
    by_cases h : i = i'
    ·
      rw [h]
    ·
      unfold y''
      simp [h]
  have h_Eq : ∀ i ∈ range n, y'' i = (y i) := by
    simp at h_y''
    intro i hi
    have hi := Lt.of.In_Range hi
    exact h_y'' i hi
  have h_Eq := EqSumS.of.All_Eq h_Eq
  have := EqSumS.of.All_Eq h_y''
  have := Eq.trans h_Eq.symm this
  rw [Finset.sum_ite] at this
  rw [this]
  repeat rw [Finset.sum_filter]
  simp [h₀]


-- created on 2025-04-06
