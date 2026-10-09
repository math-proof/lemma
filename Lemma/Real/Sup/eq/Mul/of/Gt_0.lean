import sympy.sets.sets
import sympy.Basic
import Mathlib.Data.Real.Pointwise


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a m M : ℝ}
-- given
  (h : 0 < a) :
-- imply
  sSup ((fun x => f x * a) '' Set.Ioo m M) =
    a * sSup (f '' Set.Ioo m M) := by
-- proof
  calc _ = ⨆ x : ↥(Set.Ioo m M), f ↑x * a := sSup_image'
    _ = (⨆ x : ↥(Set.Ioo m M), f ↑x) * a :=
        (Real.iSup_mul_of_nonneg h.le _).symm
    _ = a * sSup (f '' Set.Ioo m M) := by
        rw [sSup_image']
        ring


-- created on 2019-08-21
-- updated on 2023-05-14
