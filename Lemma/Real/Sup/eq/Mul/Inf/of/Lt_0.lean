import sympy.sets.sets
import sympy.Basic
import Mathlib.Data.Real.Pointwise


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a m M : ℝ}
-- given
  (h : a < 0) :
-- imply
  sSup ((fun x => f x * a) '' Set.Ioo m M) =
    a * sInf (f '' Set.Ioo m M) := by
-- proof
  calc _ = ⨆ x : ↥(Set.Ioo m M), f ↑x * a := sSup_image'
    _ = (⨅ x : ↥(Set.Ioo m M), f ↑x) * a :=
        (Real.iInf_mul_of_nonpos h.le _).symm
    _ = a * ⨅ x : ↥(Set.Ioo m M), f ↑x := by ring
    _ = a * sInf (f '' Set.Ioo m M) := by rw [sInf_image']


-- created on 2019-12-22
