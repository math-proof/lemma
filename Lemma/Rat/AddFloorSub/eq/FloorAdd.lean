import sympy.functions.elementary.integers
import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Set.Frac.in.Ico
open Int Set


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  {x : α} :
-- imply
  ⌊x - 1 / 2⌋ + 1 = ⌊x + 1 / 2⌋ := by
-- proof
  let f := fract x
  have hf := mem_Ico.mp (Frac.in.Ico (x := x))
  have hz_add : x = (⌊x⌋ : α) + f := by
    dsimp [f]
    rw [Int.fract]
    abel
  have h1 : ⌊x - 1 / 2⌋ = ⌊x⌋ + ⌊f - 1 / 2⌋ := by
    conv_lhs => rw [hz_add]
    rw [add_sub_assoc, floor_intCast_add]
  have h2 : ⌊x + 1 / 2⌋ = ⌊x⌋ + ⌊f + 1 / 2⌋ := by
    conv_lhs => rw [hz_add]
    rw [add_assoc, floor_intCast_add]
  rw [h1, h2]
  suffices ⌊f - 1 / 2⌋ + 1 = ⌊f + 1 / 2⌋ by linarith
  if hf_lt : f < 1 / 2 then
    have hfm : f - 1 / 2 < 0 := sub_neg.mpr hf_lt
    have hfm' : (-1 : α) < f - 1 / 2 := by linarith [hf.1]
    have hfl : ⌊f - 1 / 2⌋ = -1 := by
      rw [(EqFloor.is.Le.Lt (a := f - 1 / 2) (z := -1)).mpr ⟨by linarith, by linarith [hf.2]⟩]
    have hfr : ⌊f + 1 / 2⌋ = 0 := by
      rw [(EqFloor.is.Le.Lt (a := f + 1 / 2) (z := 0)).mpr ⟨by linarith [hf.1], by linarith [hf.2]⟩]
    linarith
  else
    have hf_ge : 1 / 2 ≤ f := not_lt.mp hf_lt
    have hfm : (0 : α) ≤ f - 1 / 2 := sub_nonneg.mpr hf_ge
    have hfm' : f - 1 / 2 < 1 := by linarith [hf.2]
    have hfl : ⌊f - 1 / 2⌋ = 0 := by
      rw [(EqFloor.is.Le.Lt (a := f - 1 / 2) (z := 0)).mpr ⟨(by simpa using hfm), (by simpa using hfm')⟩]
    have hfr : ⌊f + 1 / 2⌋ = 1 := by
      have hlo : (1 : α) ≤ f + 1 / 2 := by linarith [hf_ge]
      have hhi : f + 1 / 2 < (1 : α) + 1 := by linarith [hf.2]
      rw [(EqFloor.is.Le.Lt (a := f + 1 / 2) (z := 1)).mpr ⟨(by simpa using hlo), (by simpa using hhi)⟩]
    linarith


-- created on 2018-05-31
