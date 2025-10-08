import Lemma.List.LengthCartesianProduct.eq.Prod
import Lemma.List.CartesianProductNil.eq.ListNil
import Lemma.Algebra.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.LtVal
import Lemma.List.CartesianProductCons.eq.FlatMapFunMapCartesianProduct
import Lemma.List.GetFlatten_AddMul.eq.Get.of.Lt.Lt_Length.All_EqLength
open Algebra List Nat


@[main]
private lemma main
  {x s : List ℕ}
-- given
  (h₀ : x.length = s.length)
  (h₁ : ∀ i (h_x : i < x.length) (h_s : i < s.length), x[i] < s[i]) :
-- imply
  ∃ i : Fin s.cartesianProduct.length, x = s.cartesianProduct[i] := by
-- proof
  induction s generalizing x with
  | nil =>
    simp
    use ⟨0, by simp_all [LengthCartesianProduct.eq.Prod]⟩
    simp_all [CartesianProductNil.eq.ListNil]
  | cons s₀ s ih =>
    match x with
    | .nil =>
      contradiction
    | x₀ :: x =>
      simp at h₀
      have ih := ih h₀
      simp at h₁
      have h₀ := h₁ 0
      simp at h₀
      have h₁ : ∀ (i : ℕ) (h_x : i < x.length) (h_s : i < s.length), x[i] < s[i] := by 
        intro i h_x h_s
        specialize h₁ (i + 1)
        simp at h₁
        apply h₁ h_x h_s
      simp_rw [h₁] at ih
      simp at ih
      let ⟨i, hi⟩ := ih
      have h_i := LtVal i
      have h_prod := LengthCartesianProduct.eq.Prod s
      simp [h_prod] at h_i
      have : x₀ * s.prod + i < (s₀ :: s).cartesianProduct.length := by 
        simp [LengthCartesianProduct.eq.Prod]
        apply AddMul.lt.Mul.of.Lt.Lt h₀ h_i
      use ⟨x₀ * s.prod + i, this⟩
      simp [CartesianProductCons.eq.FlatMapFunMapCartesianProduct]
      unfold List.flatMap
      rw [GetFlatten_AddMul.eq.Get.of.Lt.Lt_Length.All_EqLength] <;>
      ·
        simp_all


-- created on 2025-06-14
