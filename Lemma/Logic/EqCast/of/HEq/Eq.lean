import Lemma.Basic


/--
this might conflicts with Logic.HEq.is.EqCast.of.Eq
-/
@[main, comm 3]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h₀ : m = n)
  (h₁ : HEq b a) :
-- imply
  cast (by rw [h₀]) b = a := by
-- proof
  aesop


-- created on 2025-07-25
