import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Spherical.SphericalLawOfCosines
open scoped BigOperators
open MetaMathlibExt


/--
[spherical_law_of_cosines_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Spherical/SphericalLawOfCosines.lean)
-/
@[path]
private lemma spherical_law_of_cosines_general_eq
  {a b c C : ℝ}
  {u v w : Fin 3 → ℝ}
-- given
  (ha : 0 < a ∧ a < Real.pi)
  (hb : 0 < b ∧ b < Real.pi)
  (hu : ∑ i, u i * u i = 1)
  (hv : ∑ i, v i * v i = 1)
  (hw : ∑ i, w i * w i = 1)
  (ha_side : ∑ i, v i * w i = Real.cos a)
  (hb_side : ∑ i, u i * w i = Real.cos b)
  (hc_side : ∑ i, u i * v i = Real.cos c)
  (hC_angle : Real.cos C = ((∑ i, u i * v i) - (∑ i, u i * w i) * (∑ i, v i * w i)) / (Real.sqrt (∑ i, (u i - (∑ j, u j * w j) * w i) * (u i - (∑ j, u j * w j) * w i)) * Real.sqrt (∑ i, (v i - (∑ j, v j * w j) * w i) * (v i - (∑ j, v j * w j) * w i)))) :
-- imply
  Real.cos c = Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C := by
-- proof
  apply MetaMathlibExt.spherical_law_of_cosines_general a b c C u v w ha hb hu hv hw ha_side hb_side hc_side hC_angle

/--
[spherical_law_of_cosines](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Spherical/SphericalLawOfCosines.lean)
-/
@[path]
private lemma spherical_law_of_cosines_eq
  {a b c C : ℝ}
  {u v w : Fin 3 → ℝ}
-- given
  (ha : 0 < a ∧ a < Real.pi)
  (hb : 0 < b ∧ b < Real.pi)
  (hc : 0 < c ∧ c < Real.pi)
  (hC : 0 < C ∧ C < Real.pi)
  (hu : ∑ i, u i * u i = 1)
  (hv : ∑ i, v i * v i = 1)
  (hw : ∑ i, w i * w i = 1)
  (ha_side : ∑ i, v i * w i = Real.cos a)
  (hb_side : ∑ i, u i * w i = Real.cos b)
  (hc_side : ∑ i, u i * v i = Real.cos c)
  (hC_angle : Real.cos C = ((∑ i, u i * v i) - (∑ i, u i * w i) * (∑ i, v i * w i)) / (Real.sqrt (∑ i, (u i - (∑ j, u j * w j) * w i) * (u i - (∑ j, u j * w j) * w i)) * Real.sqrt (∑ i, (v i - (∑ j, v j * w j) * w i) * (v i - (∑ j, v j * w j) * w i)))) :
-- imply
  Real.cos c = Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C := by
-- proof
  apply MetaMathlibExt.spherical_law_of_cosines a b c C u v w ha hb hc hC hu hv hw ha_side hb_side hc_side hC_angle


-- created on 2026-10-20
