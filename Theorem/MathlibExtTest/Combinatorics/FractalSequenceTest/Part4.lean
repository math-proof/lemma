/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/


import Structure.Combinatorics.FractalSequence
import Lemma.Finset.FractalSequence
import Mathlib.Tactic
import Def.MathlibExtTest.Combinatorics.FractalSequenceTest.Part3


namespace MetaMathlibExt

theorem diagPos_diagUnpair (n : ℕ) :
    diagPos (diagUnpair n).1 (diagUnpair n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [diagUnpair]
    split_ifs with hj
    · have ih' : triangle (diagUnpair n).1 + (diagUnpair n).1 = n := by
        simpa [diagPos, hj] using ih
      simp only [diagPos, zero_add]
      rw [triangle_succ]
      omega
    · have ih' : triangle ((diagUnpair n).1 + (diagUnpair n).2) +
          (diagUnpair n).1 = n := by simpa [diagPos] using ih
      simp only [diagPos]
      have hjpos : 0 < (diagUnpair n).2 := Nat.pos_of_ne_zero hj
      rw [show (diagUnpair n).1 + 1 + ((diagUnpair n).2 - 1) =
        (diagUnpair n).1 + (diagUnpair n).2 by omega]
      omega

theorem diagUnpair_diagPos (i j : ℕ) : diagUnpair (diagPos i j) = (i, j) := by
  apply diagPos_injective
  change diagPos (diagUnpair (diagPos i j)).1 (diagUnpair (diagPos i j)).2 = diagPos i j
  exact diagPos_diagUnpair (diagPos i j)

end MetaMathlibExt
