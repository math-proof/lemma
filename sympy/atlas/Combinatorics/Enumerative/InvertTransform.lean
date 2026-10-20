/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/InvertTransform.lean -/

import Mathlib.RingTheory.PowerSeries.Inverse

namespace MetaMathlibExt

/-- INVERT transform of an integer sequence (concept `jis_sem_22fea8fd5a269c1828606fd8`;
source statements `jis_bdc94f3dcf45a8b11a488c9a`, `jis_fa06f78544747f9465a909ce`,
`jis_a1ec2137c84e5b9b5ce1f3f7`, `jis_dc5074e4bf1c7aedd3a999d3`).
Lean index `n` denotes source index `n+1` for both input and output.
The input ordinary generating function is embedded as `X * mk a`, whose constant
coefficient is zero, and the output is read off degrees `n+1` of the inverse of
`1 - X * mk a` obtained by `invOfUnit` with the unit `1` over `Int`. -/
noncomputable def invertTransform (a : ℕ → ℤ) : ℕ → ℤ :=
  fun n => PowerSeries.coeff (n + 1) ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1)

/-- Generating-function characterization of the INVERT transform
(concept `jis_sem_22fea8fd5a269c1828606fd8`): `1 + B(t)` is the multiplicative
inverse of `1 - A(t)`, where `A(t) = X * mk a` and `B(t) = X * mk (invertTransform a)`. -/
theorem invertTransform_spec (a : ℕ → ℤ) :
    (1 - PowerSeries.X * PowerSeries.mk a) *
      (1 + PowerSeries.X * PowerSeries.mk (invertTransform a)) = 1 := by
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
    rw [hmk, add_comm]
    exact hdecomp.symm
  calc (1 - PowerSeries.X * PowerSeries.mk a) *
        (1 + PowerSeries.X * PowerSeries.mk (invertTransform a))
      = (1 - PowerSeries.X * PowerSeries.mk a) *
        ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1) := by
          rw [h_eq]
    _ = 1 := PowerSeries.mul_invOfUnit _ _ hφ

end MetaMathlibExt
