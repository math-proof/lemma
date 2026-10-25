/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch9Entry22Chudnovsky.lean -/


import Def.Analysis.Ramanujan.Part1Ch9Entry22Chudnovsky
import Lemma.Real.Ramanujan.Part1Ch9Entry22Chudnovsky


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch9Entry22Chudnovsky

open MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry22Chudnovsky

example :
    chapter9Chi3Term =
      MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry21Piseries2.chapter9Chi3Term :=
  chapter9Chi3Term_eq_entry21

example :
    MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry21Piseries2.chapter9Chi3AtOne =
      chapter9Chi3AtOne :=
  chapter9Chi3AtOne_eq_entry21.symm

example :
    chapter9Entry23FactorialTerm =
      MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry20Piseries1.chapter9Entry23FactorialTerm :=
  chapter9Entry23FactorialTerm_eq_entry20

-- Local interval hypotheses suffice to invoke Entry 22.
example (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 < 2 * Real.cos x :=
  (ramanujan_part1_ch9_entry22_chudnovsky x hx0 hx).1

end MathlibExtTest.Analysis.Ramanujan.Part1Ch9Entry22Chudnovsky
