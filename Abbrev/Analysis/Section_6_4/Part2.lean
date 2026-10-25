import Mathlib
import Abbrev.Analysis.Section_6_3
import Theorem.Analysis.Section_6_4


namespace Chapter6

open EReal

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]

end Chapter6
