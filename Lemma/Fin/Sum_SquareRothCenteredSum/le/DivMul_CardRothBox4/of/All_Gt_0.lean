import Mathlib
import Lemma.Fin.Sum_SquareRothCentered.le.DivCardRothBox4.of.All_Gt_0
import Lemma.Fin.Sum_MulRothSCentered.eq.Zero.of.Ne.All_Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothCentered_second_moment_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {r : Fin m → ℕ}
-- given
  (hr : ∀ h, 0 < r h) :
-- imply
  ∑ j : RothBox r, rothCenteredSum r j ^ 2 ≤
    (m : ℝ) * Fintype.card (RothBox r) / 4 := by
-- proof
  have hexpand :
    (∑ j : RothBox r, rothCenteredSum r j ^ 2) =
      ∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
        rothCentered r j h * rothCentered r j k := calc
      _ = ∑ j : RothBox r, ∑ h : Fin m, ∑ k : Fin m,
            rothCentered r j h * rothCentered r j k := by
        apply Finset.sum_congr rfl
        intro j _
        unfold rothCenteredSum
        rw [pow_two, Finset.sum_mul_sum]
      _ = ∑ h : Fin m, ∑ j : RothBox r, ∑ k : Fin m,
            rothCentered r j h * rothCentered r j k := Finset.sum_comm
      _ = ∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
            rothCentered r j h * rothCentered r j k := by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_comm
  rw [hexpand]
  calc
    _ ≤ ∑ h : Fin m, ∑ k : Fin m,
          if h = k then (Fintype.card (RothBox r) : ℝ) / 4 else 0 := by
      gcongr with h k
      if hhk : h = k then
        subst k
        simpa [pow_two] using Sum_SquareRothCentered.le.DivCardRothBox4.of.All_Gt_0 hr h
      else
        simp only [hhk, ↓reduceIte]
        rw [Sum_MulRothSCentered.eq.Zero.of.Ne.All_Gt_0 hr hhk]
    _ = (m : ℝ) * Fintype.card (RothBox r) / 4 := by
      simp
      ring


-- created on 2026-10-21
