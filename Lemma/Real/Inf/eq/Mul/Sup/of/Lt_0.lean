import sympy.sets.sets
import sympy.Basic
import Mathlib.Data.Real.Pointwise


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a m M : ℝ}
-- given
  (h : a < 0) :
-- imply
  sInf ((fun x => f x * a) '' Set.Ioo m M) = a * sSup (f '' Set.Ioo m M) := by
-- proof
  calc _ = ⨅ x : ↥(Set.Ioo m M), f ↑x * a := sInf_image'
    _ = a * ⨆ x : ↥(Set.Ioo m M), f ↑x := by
        rw [← Real.iSup_mul_of_nonpos h.le (f := fun (x : ↥(Set.Ioo m M)) => f ↑x)]
        exact mul_comm _ _
    _ = a * sSup (f '' Set.Ioo m M) := by rw [sSup_image']


-- created on 2019-12-22
-- updated on 2021-10-02
