import Lemma.Int.GeFloor.is.Ge
import Lemma.Int.LeCeil.is.Le
import Lemma.Set.In_Icc.is.Le.Le
open Set Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {x a b d : ℤ}
-- given
  (h_d : d > 0)
  (h : d * x ∈ Icc a b) :
-- imply
  x ∈ Icc ⌈(a / d : α)⌉ (⌊(b / d : α)⌋) := by
-- proof
  obtain ⟨h_ge, h_dx_le_b⟩ := (In_Icc.is.Le.Le _ _).mp h
  have hd' : (0 : α) < d := by exact_mod_cast h_d
  apply In_Icc.of.Le.Le
  ·
    have h_a_div_le : (a : α) / d ≤ (x : α) := by
      rw [div_le_iff₀ hd']
      exact_mod_cast (by simpa [mul_comm] using h_ge)
    exact LeCeil.of.Le h_a_div_le
  ·
    have h_x_le_div : (x : α) ≤ (b : α) / d := by
      rw [le_div_iff₀ hd']
      exact_mod_cast (by simpa [mul_comm] using h_dx_le_b)
    exact GeFloor.of.Ge h_x_le_div

-- created on 2018-05-24
