import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.InvertTransform
open MetaMathlibExt


namespace MetaMathlibExt

/--
[invertTransform_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/InvertTransform.lean)
-/
@[path]
lemma invertTransform_spec
  {a : ℕ → ℤ} :
-- imply
  (1 - PowerSeries.X * PowerSeries.mk a) *
      (1 + PowerSeries.X * PowerSeries.mk (invertTransform a)) = 1 := by
-- proof
  have hφ : PowerSeries.constantCoeff (1 - PowerSeries.X * PowerSeries.mk a) =
    ((1 : ℤˣ) : ℤ) := by
    simp
  have hC : PowerSeries.C
    (PowerSeries.constantCoeff
      ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1)) = 1 := by
    simp [PowerSeries.constantCoeff_invOfUnit]
  have hdecomp := PowerSeries.eq_X_mul_shift_add_const
    ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1)
  rw [hC] at hdecomp
  have hmk : PowerSeries.mk (invertTransform a) =
    PowerSeries.mk fun p => PowerSeries.coeff (p + 1)
      ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1) := rfl
  have h_eq : (1 : PowerSeries ℤ) + PowerSeries.X * PowerSeries.mk (invertTransform a)
    = (1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1 := by
    rwa [hmk, add_comm]
  calc (1 - PowerSeries.X * PowerSeries.mk a) *
    (1 + PowerSeries.X * PowerSeries.mk (invertTransform a))
    = (1 - PowerSeries.X * PowerSeries.mk a) *
      ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1) := by
        rw [h_eq]
    _ = 1 := PowerSeries.mul_invOfUnit _ _ hφ

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
