import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.VanSchooten
open MetaMathlibExt


/--
[vanSchooten_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/VanSchooten.lean)
-/
@[path]
private lemma vanSchooten_general_eq
  {A B C P O : EuclideanSpace ℝ (Fin 2)}
  {r : ℝ}
-- given
  (hr : 0 < r)
  (he1 : dist A B = dist B C)
  (he2 : dist B C = dist C A)
  (hA : A ∈ Metric.sphere O r)
  (hB : B ∈ Metric.sphere O r)
  (hC : C ∈ Metric.sphere O r)
  (hP : P ∈ Metric.sphere O r)
  (h0 : dist C P > dist A P)
  (h1 : dist C P > dist B P) :
-- imply
  dist P A + dist P B = dist P C := by
-- proof
  apply MetaMathlibExt.vanSchooten_general A B C P O r hr he1 he2 hA hB hC hP h0 h1

/--
[vanSchooten](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/VanSchooten.lean)
-/
@[path]
private lemma vanSchooten_eq
  :
-- imply
  ∀ (A B C P O : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
    0 < r →
    dist A B = dist B C →
    dist B C = dist C A →
    A ∈ Metric.sphere O r →
    B ∈ Metric.sphere O r →
    C ∈ Metric.sphere O r →
    P ∈ Metric.sphere O r →
    P ≠ A → P ≠ B → P ≠ C →
    dist C P > dist A P →
    dist C P > dist B P →
    dist P A + dist P B = dist P C := by
-- proof
  apply MetaMathlibExt.vanSchooten


-- created on 2026-10-20
