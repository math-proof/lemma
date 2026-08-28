import Lemma.Complex.AbsCeilSubDivMul3Arg.le.One
import Lemma.Int.AbsAdd.le.AddAbsS
import Lemma.Int.AbsNeg.eq.Abs
import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Nat.LeAddS.of.Le.Le
open Complex Int Nat


@[main]
private lemma main
-- given
  (z w : ℂ) :
-- imply
  |⌈3 * arg z / (2 * π) - 1 / 2⌉ - ⌈3 * arg w / (2 * π) - 1 / 2⌉| ≤ 2 := calc
-- proof
  _ ≤ |⌈3 * arg z / (2 * π) - 1 / 2⌉| + |-⌈3 * arg w / (2 * π) - 1 / 2⌉| := by
    rw [Sub.eq.Add_Neg]
    apply AbsAdd.le.AddAbsS
  _ = |⌈3 * arg z / (2 * π) - 1 / 2⌉| + |⌈3 * arg w / (2 * π) - 1 / 2⌉| := by
    rw [AbsNeg.eq.Abs]
  _ ≤ 1 + 1 := by
    apply LeAddS.of.Le.Le
    ·
      apply AbsCeilSubDivMul3Arg.le.One
    ·
      apply AbsCeilSubDivMul3Arg.le.One
  _ = 2 := by
    norm_num


-- created on 2026-08-28
