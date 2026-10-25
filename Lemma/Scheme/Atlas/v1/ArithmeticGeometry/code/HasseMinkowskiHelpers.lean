import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.HasseMinkowski
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HasseMinkowski


/--
[wss_vec3_generic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiHelpers.lean)
-/
@[path]
lemma wss_vec3_generic
  [CommSemiring k]
  {w₀ w₁ w₂ x₀ x₁ x₂ : k} :
-- imply
  QuadraticMap.weightedSumSquares k ![w₀, w₁, w₂] ![x₀, x₁, x₂] = w₀ * (x₀ * x₀) + w₁ * (x₁ * x₁) + w₂ * (x₂ * x₂) := by
-- proof
  simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul]

/--
[wss_vec3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiHelpers.lean)
-/
@[path]
lemma wss_vec3
  {w₀ w₁ w₂ x₀ x₁ x₂ : ℝ} :
-- imply
  QuadraticMap.weightedSumSquares ℝ ![w₀, w₁, w₂] ![x₀, x₁, x₂] = w₀ * (x₀ * x₀) + w₁ * (x₁ * x₁) + w₂ * (x₂ * x₂) :=
-- proof
  wss_vec3_generic w₀ w₁ w₂ x₀ x₁ x₂

/--
[vec3_ne_zero_of_idx0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiHelpers.lean)
-/
@[path]
lemma vec3_ne_zero_of_idx0
  [Zero α]
  {a b c : α}
-- given
  (ha : a ≠ 0) :
-- imply
  ![a, b, c] ≠ 0 := by
-- proof
  intro h; exact ha (by have := congr_fun h 0; simpa using this)

/--
[vec3_ne_zero_of_idx1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiHelpers.lean)
-/
@[path]
lemma vec3_ne_zero_of_idx1
  [Zero α]
  {a b c : α}
-- given
  (hb : b ≠ 0) :
-- imply
  ![a, b, c] ≠ 0 := by
-- proof
  intro h; exact hb (by have := congr_fun h 1; simpa using this)

/--
[vec3_ne_zero_of_idx2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiHelpers.lean)
-/
@[path]
lemma vec3_ne_zero_of_idx2
  [Zero α]
  {a b c : α}
-- given
  (hc : c ≠ 0) :
-- imply
  ![a, b, c] ≠ 0 := by
-- proof
  intro h; exact hc (by have := congr_fun h 2; simpa using this)


-- created on 2026-10-23
