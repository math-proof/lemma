import Lemma.Int.Sub.eq.Zero.is.Eq
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : fract x = 0) :
-- imply
  x ∈ Set.range Int.cast := by
-- proof
  use ⌊x⌋
  apply Eq.symm
  apply Eq.of.Sub.eq.Zero
  unfold Int.fract at h
  assumption


-- created on 2025-04-04
