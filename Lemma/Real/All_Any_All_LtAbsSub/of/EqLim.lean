import Lemma.Real.EqLim.is.All_Any_All_LtAbsSub


@[path]
private lemma main
  [LinearOrder α]
  [Zero α]
  [One α]
  [NoMaxOrder α]
  [ZeroLEOneClass α]
  [NeZero (1 : α)]
-- given
  (f : α → ℝ)
  (a : ℝ)
  (h : lim [x → ∞] f x = a) :
-- imply
  ∀ ε > 0, ∃ N > 0, ∀ x > N, |f x - a| < ε := by
-- proof
  exact Real.All_Any_All_LtAbsSub.of.EqLim.εN.pos h


-- created on 2026-10-03
