import Lemma.Bool.SEq.is.Eq
import Lemma.Int.EqNegToNatNeg.of.Lt_0
import Lemma.Int.EqToNat.of.Ge_0
import Lemma.List.EqPermute
import Lemma.Tensor.MapCast.as.Map.of.Eq
import Lemma.Tensor.PermuteMap.eq.MapPermute.of.GtLength
import Lemma.Tensor.PermuteMap.eq.MapPermute__Neg.of.GtLength_Add
import Lemma.Tensor.SEqPermute
import Lemma.Tensor.SEqPermuteS.of.Add.ge.SubLength_1
import Lemma.Tensor.SEqPermuteS__Neg.of.Le
open Tensor Bool Int List


@[main]
private lemma main
  {f : α → β}
-- given
  (X : Tensor α s)
  (i : Fin s.length)
  (d : ℤ) :
-- imply
  (X.map f).permute i d ≃ (X.permute i d).map f := by
-- proof
  if h_d : d ≥ 0 then
    have h_toNat := EqToNat.of.Ge_0 h_d
    by_cases h_zero : d = 0
    · subst h_zero
      have h_X_map := SEqPermute (i := i) (s := s) (α := β) (X.map f)
      have h_s := Eq_Permute i
      exact h_X_map.trans (SEq.symm (MapCast.as.Map.of.Eq h_s (X := X) (f := f)))
    ·
      have h_pos := PermuteMap.eq.MapPermute.of.GtLength
        (h_i := by grind) (i := i) (X := X) (d := d.toNat) (f := f)
      exact h_toNat ▸ h_pos
  else
    have h_neg : d < 0 := by omega
    have h_toNat := EqNegToNatNeg.of.Lt_0 h_neg
    if h_bound : i ≥ (-d).toNat then
      let k := (-d).toNat
      have h_idx : i = ⟨↑i - k + k, by grind⟩ := Fin.ext (by grind)
      have h := PermuteMap.eq.MapPermute__Neg.of.GtLength_Add (i := i - k) (d := k) (h_i := by grind) (X := X) (f := f)
      rw [← h_idx] at h
      have h_off : (-↑k : ℤ) = d := by grind
      rw [h_off] at h
      exact h
    else
      have h_X := SEqPermuteS__Neg.of.Le (i := i) (d := (-d).toNat) (by grind) X
      have h_X_map := SEqPermuteS__Neg.of.Le (i := i) (d := (-d).toNat) (by grind) (X.map f)
      rw [h_toNat] at h_X h_X_map
      have h_X' : X.permute i d ≃ X.permute i (-i) := by simpa using h_X
      have h_reduced := main (X := X) (i := i) (d := -i) (f := f)
      refine h_X_map.trans (h_reduced.trans ?_)
      apply (MapCast.as.Map.of.Eq h_X'.symm.1 (X := X.permute i (-i)) (f := f)).symm.trans (SEq.of.Eq (congrArg (Tensor.map f) (SEq.cast h_X'.symm)))


-- created on 2026-08-07
