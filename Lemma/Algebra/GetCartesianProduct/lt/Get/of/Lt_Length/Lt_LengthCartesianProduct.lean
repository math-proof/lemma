import Lemma.Algebra.CartesianProductCons.eq.FlatMapFunMapCartesianProduct
import Lemma.Algebra.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.Algebra.Gt_0.of.Ne_0
import Lemma.Algebra.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Algebra.GetFlatten_AddMul.eq.Get.of.Lt.Lt_Length.All_EqLength
import Lemma.Algebra.LengthGetCartesianProduct.eq.Length.of.Lt_LengthCartesianProduct
open Algebra


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h₀ : i < s.cartesianProduct.length)
  (h₂ : j < s.length) :
-- imply
  have : j < s.cartesianProduct[i].length := by
    rwa [← LengthGetCartesianProduct.eq.Length.of.Lt_LengthCartesianProduct] at h₂
  s.cartesianProduct[i][j] < s[j] := by
-- proof
  intro h₁
  induction s generalizing i j with
  | nil =>
    unfold List.cartesianProduct at *
    contradiction
  | cons s₀ s ih =>
    simp [CartesianProductCons.eq.FlatMapFunMapCartesianProduct] at h₀ h₁
    let ⟨k, hk, t, ht, h_eq⟩ := Any_Eq_AddMul.of.Lt_Mul h₀
    simp at h₂
    simp [CartesianProductCons.eq.FlatMapFunMapCartesianProduct]
    unfold List.flatMap
    simp [h_eq]
    let v := (List.range s₀).map (fun h ↦ s.cartesianProduct.map (fun t ↦ h :: t))
    have h_v : v = (List.range s₀).map (fun h ↦ s.cartesianProduct.map (fun t ↦ h :: t)) := rfl
    simp [← h_v]
    have h_k : k < v.length := by
      simp_all
    have h_t : t < s.cartesianProduct.length := by
      simp_all
    have h_v : ∀ l ∈ v, l.length = s.cartesianProduct.length := by
      simp [v]
    simp [GetFlatten_AddMul.eq.Get.of.Lt.Lt_Length.All_EqLength h_v h_k h_t]
    by_cases h : j = 0
    ·
      simp_all
    ·
      have h := Gt_0.of.Ne_0 h
      rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0 (by assumption)]
      simp [v]
      rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0 (by assumption)]
      simp [ih]


-- created on 2025-06-14
-- updated on 2025-06-29
