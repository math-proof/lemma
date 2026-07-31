import Lemma.Set.Frac.in.Ioo.of.NotIn_Range
import Lemma.Set.Neg.in.Ioo.of.In_Ioo
open Set


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∉ range Int.cast) :
-- imply
  ⌊-fract x⌋ = -1 := by
-- proof
  have h₁ := Frac.in.Ioo.of.NotIn_Range h
  have h₂ := Neg.in.Ioo.of.In_Ioo h₁
  obtain ⟨h₂₀, h₂₁⟩ := h₂
  rw [Int.floor_eq_iff]
  constructor
  ·
    exact_mod_cast h₂₀.le
  ·
    norm_cast
    grind


-- created on 2018-05-20
