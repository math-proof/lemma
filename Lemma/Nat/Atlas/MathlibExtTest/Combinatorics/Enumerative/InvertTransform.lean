import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Combinatorics.Enumerative.InvertTransform
open MetaMathlibExt


/--
[invertTransform_zero_0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/InvertTransform.lean)
-/
@[path]
private lemma invertTransform_zero_0 : invertTransform (fun _ => (0 : ℤ)) 0 = 0 := by
  rw [invertTransform, PowerSeries.coeff_invOfUnit]
  simp [Finset.antidiagonal]

/--
[invertTransform_zero_1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/InvertTransform.lean)
-/
@[path]
private lemma invertTransform_zero_1 : invertTransform (fun _ => (0 : ℤ)) 1 = 0 := by
  rw [invertTransform, PowerSeries.coeff_invOfUnit]
  simp [Finset.antidiagonal]

/--
[invertTransform_one_0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/InvertTransform.lean)
-/
@[path]
private lemma invertTransform_one_0 : invertTransform (fun _ => (1 : ℤ)) 0 = 1 := by
  rw [invertTransform, PowerSeries.coeff_invOfUnit]
  simp [Finset.antidiagonal]

/--
[invertTransform_one_1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/InvertTransform.lean)
-/
@[path]
private lemma invertTransform_one_1 : invertTransform (fun _ => (1 : ℤ)) 1 = 2 := by
  have h0 := invertTransform_one_0
  change PowerSeries.coeff 1
    ((1 - PowerSeries.X * PowerSeries.mk fun _ => (1 : ℤ)).invOfUnit 1) = 1 at h0
  rw [invertTransform, PowerSeries.coeff_invOfUnit]
  simp [Finset.antidiagonal, h0]


-- created on 2026-10-23
