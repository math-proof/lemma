import Lemma.Finset.All_Le.of.All_Le.All_Eq_Ite
import Lemma.Finset.Sum.eq.Sum_Add_Sub.of.In_Range.All_Eq_Ite
import Lemma.Int.Lt.is.Gt0Sub
import Lemma.Int.Lt.of.Eq_Add.Lt_0
import Lemma.Finset.LeSumS.of.All_Le
import Lemma.Nat.Lt.of.Le.Lt
open Finset Nat Int


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
    if h : i = i' then
      rw [h]
    else
      unfold y'
      simp [h]
  apply Lt.of.Le.Lt
  .
    apply LeSumS.of.All_Le
    apply All_Le.of.All_Le.All_Eq_Ite h_In h₀ h_y'
  .
    apply Lt.of.Eq_Add.Lt_0
    .
      apply Sum.eq.Sum_Add_Sub.of.In_Range.All_Eq_Ite h_In h_y'
    .
      apply Gt0Sub.of.Lt h_Lt


-- created on 2025-04-06
