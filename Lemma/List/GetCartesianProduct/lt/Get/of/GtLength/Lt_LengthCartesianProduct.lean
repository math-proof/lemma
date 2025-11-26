import Lemma.List.CartesianProductCons.eq.FlatMap_FunMapCartesianProduct
import Lemma.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.GetFlatten_AddMul.eq.Get.of.Lt.GtLength.All_EqLength
import Lemma.List.LengthGetCartesianProduct.eq.Length.of.Lt_LengthCartesianProduct
open List Nat


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
    simp [CartesianProductCons.eq.FlatMap_FunMapCartesianProduct] at h₀ h₁
    let ⟨k, hk, t, ht, h_eq⟩ := Any_Eq_AddMul.of.Lt_Mul h₀
    simp at h₂
    simp [CartesianProductCons.eq.FlatMap_FunMapCartesianProduct]
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
    simp [GetFlatten_AddMul.eq.Get.of.Lt.GtLength.All_EqLength h_v h_k h_t]
    if h : j = 0 then
      simp_all
    else
      have h := Gt_0.of.Ne_0 h
      rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0 (by assumption)]
      simp [v]
      rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0 (by assumption)]
      simp [ih]


-- created on 2025-06-14
-- updated on 2025-06-29
