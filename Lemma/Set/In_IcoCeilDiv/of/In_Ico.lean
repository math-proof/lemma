import Lemma.Int.GeFloor.is.Ge
import Lemma.Int.LeCeil.is.Le
import Lemma.Set.Ge.Le_Sub_1.of.In_Ico
import Lemma.Set.In_Ico.is.Le.Lt
import Lemma.Nat.Lt_Add_1.of.Le
open Set Int Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {x a b d : ℤ}
-- given
  (h_d : d > 0)
  (h : d * x ∈ Ico a (b + 1)) :
-- imply
  x ∈ Ico ⌈(a / d : α)⌉ (⌊(b / d : α)⌋ + 1) := by
-- proof
  obtain ⟨h_ge, h_le⟩ := Ge.Le_Sub_1.of.In_Ico h
  have h_dx_le_b : d * x ≤ b := by
    simpa using h_le
  have hd' : (0 : α) < d := by exact_mod_cast h_d
  apply In_Ico.of.Le.Lt
  ·
    have h_a_div_le : (a : α) / d ≤ (x : α) := by
      rw [div_le_iff₀ hd']
      exact_mod_cast (by simpa [mul_comm] using h_ge)
    exact LeCeil.of.Le h_a_div_le
  ·
    have h_x_le_div : (x : α) ≤ (b : α) / d := by
      rw [le_div_iff₀ hd']
      exact_mod_cast (by simpa [mul_comm] using h_dx_le_b)
    have h_x_le_floor : x ≤ ⌊(b / d : α)⌋ := GeFloor.of.Ge h_x_le_div
    exact Lt_Add_1.of.Le h_x_le_floor

-- created on 2018-05-24
