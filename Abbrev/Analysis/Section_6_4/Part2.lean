module
public import Mathlib
public import Abbrev.Analysis.Section_6_3
public import Theorem.Analysis.Section_6_4


public section

namespace Chapter6

open EReal

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]

end Chapter6
