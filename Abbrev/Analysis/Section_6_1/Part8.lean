import Mathlib
import Theorem.Analysis.Section_5_1.Part9
import Theorem.Analysis.Section_5_3.Part12
import Theorem.Analysis.Section_5_epilogue.Part5
import Theorem.Analysis.Section_6_1.Part6


namespace Chapter6

@[coe]
abbrev Sequence.ofChapter5Sequence (a: Chapter5.Sequence) : Sequence :=
{
  m := a.n₀
  seq n := a n
  vanish n hn := by simp [a.vanish n hn]
}

end Chapter6
