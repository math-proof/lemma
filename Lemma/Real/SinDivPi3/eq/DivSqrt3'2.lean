import sympy.functions.elementary.trigonometric
import sympy.Basic


/--
This lemma confirms that the sine of π/3 radians (60 degrees) is equal to √3 divided by 2, a fundamental value in trigonometry.
The proof utilizes established trigonometric identities and numerical simplification to verify this equality.
-/
@[main]
private lemma main:
-- imply
  sin (π / 3) = √3 / 2 := by
-- proof
  norm_num [Real.sin_pi_div_three]
  -- rfl


-- created on 2025-03-24
