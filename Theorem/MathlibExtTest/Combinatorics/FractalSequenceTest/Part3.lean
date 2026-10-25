/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/


import Structure.Combinatorics.FractalSequence
import Lemma.Finset.FractalSequence
import Mathlib.Tactic
import Def.MathlibExtTest.Combinatorics.FractalSequenceTest.Part2


namespace MetaMathlibExt

theorem diagPos_strict_right (i : ℕ) : StrictMono (diagPos i) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [diagPos]
  rw [show i + (j + 1) = (i + j) + 1 by omega, triangle_succ]
  omega

theorem diagPos_strict_left (j : ℕ) : StrictMono (fun i => diagPos i j) := by
  apply strictMono_nat_of_lt_succ
  intro i
  simp only [diagPos]
  rw [show i + 1 + j = (i + j) + 1 by omega, triangle_succ]
  omega

theorem diagPos_injective : Function.Injective (Function.uncurry diagPos) := by
  rintro ⟨i, j⟩ ⟨h, k⟩ heq
  change diagPos i j = diagPos h k at heq
  have hij_lo : triangle (i + j) ≤ diagPos i j := by simp [diagPos]
  have hij_hi : diagPos i j < triangle (i + j + 1) := by
    simp only [diagPos, triangle_succ]
    omega
  have hhk_lo : triangle (h + k) ≤ diagPos h k := by simp [diagPos]
  have hhk_hi : diagPos h k < triangle (h + k + 1) := by
    simp only [diagPos, triangle_succ]
    omega
  have hsum : i + j = h + k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstep : triangle (i + j + 1) ≤ triangle (h + k) :=
        triangle_strict.monotone (by omega)
      omega
    · have hstep : triangle (h + k + 1) ≤ triangle (i + j) :=
        triangle_strict.monotone (by omega)
      omega
  have hi : i = h := by
    unfold diagPos at heq
    rw [hsum] at heq
    omega
  exact Prod.ext hi (by omega)

end MetaMathlibExt
