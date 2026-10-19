import Lemma.Real.Any.All.of.IsLimited.limit_definition
open Real


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
  (A : ℝ)
  (h : lim [x → ∞] f x = A) :
-- imply
  ∀ ε > 0, ∃ N > 0, ∀ x > N, |f x - A| < ε := by
-- proof
  apply Any.All.of.IsLimited.limit_definition f A h


-- created on 2026-10-11
