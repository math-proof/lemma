import Lemma.Real.CosSub.eq.AddCosCos_SinSin
import Lemma.Real.Eq_DivPi2.of.EqCos_0.In_Icc0Pi
import Lemma.Real.GtPi0
import Lemma.Set.Ge.of.In_Icc
import Lemma.Set.In_Icc.is.Le.Le
import Lemma.Set.Le.of.In_Ico
import Lemma.Set.Lt.of.In_Ico
import Lemma.Rat.Sub_Mul_FloorDiv.in.Ico.of.Gt_0
open Real Set Rat


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : cos x = 0) :
-- imply
  x = π * ⌊x / π⌋ + π / 2 := by
-- proof
  set y := x - π * ⌊x / π⌋ with hy
  have hIco : y ∈ Ico 0 π := by simpa [hy] using Sub_Mul_FloorDiv.in.Ico.of.Gt_0 GtPi0 (n := x) (d := π)
  calc
    _ = π * ⌊x / π⌋ + y := by
      rw [hy]
      ring
    _ = π * ⌊x / π⌋ + π / 2 := by
      rw [Eq_DivPi2.of.EqCos_0.In_Icc0Pi (In_Icc.of.Le.Le (Le.of.In_Ico hIco) (le_of_lt (Lt.of.In_Ico hIco))) _]
      rw [hy, CosSub.eq.AddCosCos_SinSin, h, zero_mul]
      simp [sin_int_mul_pi, mul_comm π]

-- created on 2026-08-03
