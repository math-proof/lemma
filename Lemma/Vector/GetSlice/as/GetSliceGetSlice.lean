import Lemma.Vector.GtMin.of.GtLengthSlice
import Lemma.List.LengthSlice.eq.Min
import Lemma.List.LengthSlice.eq.Zero
import Lemma.Int.EqToNat
import Lemma.List.GetSlicedIndices.eq.AddMul.of.GtLength.Gt_0.Le.Lt
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.Mul.lt.MulToNatCeilDivSub.of.GtSub.Gt_0.Lt
import Lemma.Rat.Div.le.Zero.of.Le_0
import Lemma.Rat.EqToNatCeil_0.of.Le
import Lemma.Rat.LeToNatCeil_1.of.Le_Add
import Lemma.Vector.GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SEq.of.Eq_0.Eq_0
import Lemma.Nat.Add_Mul.eq.Add_MulAddDiv
import Lemma.Vector.LtGetSlicedIndices.of.GtLength.Gt_0.Le.Lt
import Lemma.List.AddDiv.lt.LengthSlice.of.Gt_0
open List Vector Int Nat Rat Slice


private lemma inner_slice_length
  {d : ℕ}
-- given
  (h_d : d > 0)
  (a b n : ℕ) :
-- imply
  (⟨(a / d : ℕ), (a / d + (⟨a, b, d⟩ : Slice).length n : ℕ), 1⟩ : Slice).length ((⟨(a % d : ℕ), (n : ℕ), (d : ℕ)⟩ : Slice).length n) = (⟨a, b, d⟩ : Slice).length n := by
-- proof
  set L := (⟨a, b, d⟩ : Slice).length n with hL
  set len_g := (⟨(a % d : ℕ), (n : ℕ), (d : ℕ)⟩ : Slice).length n with hlen_g
  by_cases hL0 : L = 0
  ·
    rw [hL0]
    unfold Slice.length
    simp only [EqAdd_Mul_DivSub1Sign_2, EqToNat]
    apply EqToNatCeil_0.of.Le
    simp
  ·
    have hLpos : L > 0 := Nat.pos_of_ne_zero hL0
    have h_upper : a / d + L ≤ len_g := by
      have h_idx := List.AddDiv.lt.LengthSlice.of.Gt_0 h_d ⟨L - 1, by rw [← hL]; exact Nat.sub_one_lt_of_lt hLpos⟩
      have : a / d + (L - 1) < len_g := by
        simpa [hlen_g] using h_idx
      omega
    unfold Slice.length
    simp only [EqAdd_Mul_DivSub1Sign_2, EqToNat, min_eq_left h_upper]
    have h_sub : ((a / d + L : ℕ) : ℚ) - ↑(a / d) = ↑L := by
      push_cast
      ring
    rw [h_sub]
    have h_div : (↑L : ℚ) / ↑(1 : ℕ) = ↑L := by norm_num
    rw [h_div]
    simp [Int.ceil_natCast]


@[main]
private lemma main
-- given
  (f : List.Vector α n)
  (a b d : ℕ) :
-- imply
  f[a: b: d] ≃ f[(a % d : ℕ): n: d][(a / d : ℕ): (a / d + (⟨a, b, d⟩ : Slice).length n : ℕ): 1] := by
-- proof
  if h_d : d = 0 then
    subst h_d
    apply SEq.of.Eq_0.Eq_0
    ·
      apply List.LengthSlice.eq.Zero
    ·
      simp [Nat.div_zero, List.LengthSlice.eq.Zero]
      convert LengthSlice.eq.Min (n := 0) (m := 0) <;> simp
  else
    have h_d := Nat.pos_of_ne_zero h_d
    set L := (⟨a, b, d⟩ : Slice).length n with hL
    set len_g := (⟨(a % d : ℕ), (n : ℕ), (d : ℕ)⟩ : Slice).length n with hlen_g
    have h_len_eq := inner_slice_length h_d a b n
    apply SEq.of.All_EqGetS.Eq h_len_eq.symm
    intro i
    have h_cast : (⟨(a / d : ℕ), (a / d + L : ℕ), 1⟩ : Slice).length len_g = L := by simpa [hL, hlen_g] using h_len_eq
    unfold List.Vector.getSlice
    simp only [GetElem.getElem, List.Vector.get_map]
    congr 1
    apply Fin.eq_of_val_eq
    let j := Fin.cast h_cast.symm i
    let k := (List.Vector.indices ⟨(a / d : ℕ), (a / d + L : ℕ), 1⟩ len_g).get j
    calc
      _ = (Add_Mul_DivSub1Sign_2 n a).toNat + d * i.val := by simpa [GetElem.getElem] using GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0 (N := n) (a := a) (b := b) (d := d) h_d i
      _ = a + i.val * d := by simp [EqAdd_Mul_DivSub1Sign_2, Nat.mul_comm]
      _ = a % d + (a / d + i.val) * d := Add_Mul.eq.Add_MulAddDiv a d i.val
      _ = a % d + k.val * d := by
        congr 2
        have h_inner := GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0 (N := len_g) (a := (a / d : ℕ)) (b := (a / d + L : ℕ)) (d := 1) Nat.one_pos j
        rw [EqAdd_Mul_DivSub1Sign_2 (i := a / d), EqToNat, one_mul] at h_inner
        have hk : k.val = ((List.Vector.indices ⟨(a / d : ℕ), (a / d + L : ℕ), (1 : ℕ)⟩ len_g)[j]).val := by simp [k, GetElem.getElem]
        rw [hk, h_inner]
        simp [j]
      _ = (Add_Mul_DivSub1Sign_2 n (↑a % ↑d)).toNat + d * k.val := by grind [Slice.Add_Mul_DivSub1Sign_2]
      _ = ((List.Vector.indices ⟨(a % d : ℕ), (n : ℕ), (d : ℕ)⟩ n).get k).val := by simpa [GetElem.getElem] using AddToNatAdd_Mul_DivSub1Sign_2.eq.GetIndices.of.Gt_0 (N := n) (a := (a % d : ℕ)) (b := n) (d := d) h_d k


-- created on 2026-08-07
-- updated on 2026-08-24
