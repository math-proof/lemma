import sympy.functions.elementary.integers
import Lemma.Set.NeFrac_0.of.NotIn
import Lemma.Set.Frac.in.Ico
import Lemma.Set.In_SDiff.of.In.Ne
import Lemma.Set.Ico.cut.Singleton.eq.Ioo
open Set


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∉ Set.range Int.cast) :
-- imply
  fract x > 0 := by
-- proof
  have h := NeFrac_0.of.NotIn h
  have := Frac.in.Ico (x := x)
  have h := In_SDiff.of.In.Ne this h
  have := Ico.cut.Singleton.eq.Ioo (a := (0 : α)) (b := 1)
  rw [this] at h
  exact h.left


-- created on 2025-04-04
