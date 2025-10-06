import sympy.functions.elementary.integers
import sympy.sets.sets
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
  fract x ∈ Ioo 0 1 := by
-- proof
  have h := NeFrac_0.of.NotIn h
  have := Frac.in.Ico (x := x)
  have := In_SDiff.of.In.Ne this h
  rwa [Ico.cut.Singleton.eq.Ioo] at this


-- created on 2025-04-04
