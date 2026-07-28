import Lemma.List.GtProdTail_0.of.GtProd_0
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Tensor.GetData.eq.GetDataGet.of.GtProd.GtLength_0
import Lemma.Tensor.GtLength
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor List


@[main, fin]
private lemma main
  {R : ∀ {m : List ℕ}, Tensor α m → Tensor α m → Prop}
  {R₀ : α → α → Prop}
  {A B : Tensor α s}
-- given
  (hDataS : ∀ {m : List ℕ} (A B : Tensor α m), R A B ↔ ∀ j : Fin m.prod, R₀ A.data[j] B.data[j])
  (h : R A B)
  (i : Fin A.length) :
-- imply
  R A[i] (B[i]'(GtLength i B)) := by
  rw [hDataS]
  intro k
  match s with
  | [] =>
    exact Fin.elim0 i
  | h₀ :: t =>
    let p := (h₀ :: t).tail.prod
    have h_s : (h₀ :: t).length > 0 := Nat.succ_pos _
    have hi : i.val < h₀ := Nat.lt_of_lt_of_eq i.isLt (Length.eq.Get_0.of.GtLength_0 h_s A)
    have hiB : i.val < B.length := GtLength i B
    have h_idx : i.val * p + k.val < (h₀ :: t).prod := by
      have hprod := Prod.eq.Mul_ProdTail.of.GtLength_0 h_s
      calc
        _ < i.val * p + p := Nat.add_lt_add_left k.isLt _
        _ = (i.val + 1) * p := by ring
        _ ≤ h₀ * p := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
        _ = (h₀ :: t).prod := by simp [p, hprod]
    have h' := (hDataS A B).mp h ⟨i.val * p + k.val, h_idx⟩
    have h_i : (h₀ :: t).prod > i.val * p + k.val := h_idx
    have hA :=
      (GetData.eq.GetDataGet.of.GtProd.GtLength_0.fin (α := α) (s := h₀ :: t) h_s h_i (X := A)).symm
    have hB :=
      GetData.eq.GetDataGet.of.GtProd.GtLength_0.fin (α := α) (s := h₀ :: t) h_s h_i (X := B)
    have hp : 0 < p := by
      simp only [p, List.tail_cons]
      exact GtProdTail_0.of.GtProd_0 (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h_idx)
    have h_div : (i.val * p + k.val) / p = i.val := by
      rw [Nat.add_comm (i.val * p) k.val, Nat.mul_comm i.val p, Nat.add_mul_div_left k.val i.val (y := p) hp,
        Nat.div_eq_of_lt k.isLt, Nat.zero_add]
    have h_mod : (i.val * p + k.val) % p = k.val := by
      rw [Nat.add_comm (i.val * p) k.val, Nat.mul_comm i.val p, Nat.add_mul_mod_self_left k.val p i,
        Nat.mod_eq_of_lt k.isLt]
    have hA' : (A.get i).data.get k = A.data.get ⟨i.val * p + k.val, h_idx⟩ := by
      dsimp [p] at hA ⊢
      grind
    have hB' : (B.get ⟨i.val, hiB⟩).data.get k = B.data.get ⟨i.val * p + k.val, h_idx⟩ := by
      dsimp [p] at hB ⊢
      grind
    have hmid : R₀ (A.data.get ⟨i.val * p + k.val, h_idx⟩) (B.data.get ⟨i.val * p + k.val, h_idx⟩) := by
      simpa [GetElem.getElem] using h'
    rw [← hA', ← hB'] at hmid
    simpa [GetElem.getElem] using hmid


-- created on 2026-07-28
