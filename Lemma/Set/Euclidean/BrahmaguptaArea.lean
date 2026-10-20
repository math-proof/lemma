import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.BrahmaguptaArea
open EuclideanGeometry Real
open MetaMathlibExt


/--
[brahmagupta_area](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/BrahmaguptaArea.lean)
-/
@[path]
private lemma brahmagupta_area_eq
  {a b c d s A e : ℝ}
  {P Q R S : EuclideanSpace ℝ (Fin 2)}
-- given
  (h_sides : dist P Q = a ∧ dist Q R = b ∧ dist R S = c ∧ dist S P = d)
  (h_diag : dist P R = e)
  (h_semi : s = (a + b + c + d) / 2)
  (h_cyclic : ∃ O : EuclideanSpace ℝ (Fin 2), dist O P = dist O Q ∧ dist O Q = dist O R ∧ dist O R = dist O S)
  (h_convex : ∃ T : EuclideanSpace ℝ (Fin 2), dist P T + dist T R = dist P R ∧ dist Q T + dist T S = dist Q S ∧ 0 < dist P T ∧ 0 < dist T R ∧ 0 < dist Q T ∧ 0 < dist T S)
  (h_area : A = Real.sqrt (((a + b + e) / 2) * (((a + b + e) / 2) - a) * (((a + b + e) / 2) - b) * (((a + b + e) / 2) - e)) + Real.sqrt (((c + d + e) / 2) * (((c + d + e) / 2) - c) * (((c + d + e) / 2) - d) * (((c + d + e) / 2) - e))) :
-- imply
  A = Real.sqrt ((s - a) * (s - b) * (s - c) * (s - d)) := by
-- proof
  apply MetaMathlibExt.brahmagupta_area a b c d s A e P Q R S h_sides h_diag h_semi h_cyclic h_convex h_area


-- created on 2026-10-20
