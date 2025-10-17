import Lemma.List.LengthPermute.eq.Length
import Lemma.Bool.IffEqS.of.Eq
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.List.GetElem.eq.None.of.Ge_Length
import Lemma.List.GetElem.eq.SomeGet.of.Lt_Length
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
import Lemma.List.GetRotate.eq.Ite.of.Le_Length.Lt_Length
open List Bool Nat


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i + d < s.length) :
-- imply
  ((s.drop i).take (d + 1)).rotate 1 = ((s.permute i d).take (d + i + 1)).drop i := by
-- proof
  ext j x
  by_cases h_j : j < (((s.drop i).take (d + 1)).rotate 1).length
  ·
    simp_all
    rw [GetElem.eq.SomeGet.of.Lt_Length]
    simp
    apply IffEqS.of.Eq
    rw [GetTake.eq.Get.of.Lt_LengthTake]
    ·
      rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
      ·
        split_ifs with h_pos h_i_0 h_i_length
        ·
          omega
        ·
          rw [GetRotate.eq.Ite.of.Le_Length.Lt_Length (by grind) (by grind)]
          simp
          split_ifs <;>
          .
            grind
        ·
          rw [GetRotate.eq.Ite.of.Le_Length.Lt_Length (by grind) (by grind)]
          simp
          split_ifs <;>
          .
            grind
        ·
          omega
      ·
        omega
      ·
        omega
    ·
      simp
      constructor
      ·
        omega
      ·
        rw [LengthPermute.eq.Length]
        omega
  ·
    simp_all
    rw [GetElem.eq.None.of.Ge_Length]
    ·
      simp
    ·
      simp
      conv =>
        arg 1
        rw [Add.comm (a := d)]
        rw [AddAdd.eq.Add_Add]
        simp
      rw [LengthPermute.eq.Length]
      omega


-- created on 2025-10-15
-- updated on 2025-10-17
