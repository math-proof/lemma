import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.MongeCircles
open MetaMathlibExt


/--
[monge_three_circles_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/MongeCircles.lean)
-/
@[path]
private lemma monge_three_circles_general_eq
  [AddCommGroup V] [Module ℝ V]
  {c₁ c₂ c₃ : V}
  {r₁ r₂ r₃ : ℝ}
-- given
  (h0 : r₁ ≠ r₂)
  (h1 : r₂ ≠ r₃)
  (h2 : r₁ ≠ r₃) :
-- imply
  Collinear ℝ ({(r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
    (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂),
    (r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁)} : Set V) := by
-- proof
  apply MetaMathlibExt.monge_three_circles_general h0 h1 h2

/--
[monge_three_circles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/MongeCircles.lean)
-/
@[path]
private lemma monge_three_circles_eq
  {c₁ c₂ c₃ : EuclideanSpace ℝ (Fin 2)}
  {r₁ r₂ r₃ : ℝ}
-- given
  (hr₁ : 0 < r₁)
  (hr₂ : 0 < r₂)
  (hr₃ : 0 < r₃)
  (h0 : r₁ ≠ r₂)
  (h1 : r₂ ≠ r₃)
  (h2 : r₁ ≠ r₃)
  (hd12 : Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₂ r₂))
  (hd23 : Disjoint (Metric.closedBall c₂ r₂) (Metric.closedBall c₃ r₃))
  (hd13 : Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₃ r₃)) :
-- imply
  Collinear ℝ ({(r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
    (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂),
    (r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁)} : Set (EuclideanSpace ℝ (Fin 2))) := by
-- proof
  apply MetaMathlibExt.monge_three_circles hr₁ hr₂ hr₃ h0 h1 h2 hd12 hd23 hd13


-- created on 2026-10-20
