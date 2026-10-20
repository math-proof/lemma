import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.CarnotInradius
open MetaMathlibExt


/--
[carnot_inradius_circumradius_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/CarnotInradius.lean)
-/
@[path]
private lemma carnot_inradius_circumradius_general_eq
  :
-- imply
  {V : Type*} {P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)]
    (A B C O I : P) (R r x y z : ℝ)
    (nBC nCA nAB : V)
    (hTri : ¬ Collinear ℝ ({A, B, C} : Set P))
    (hRpos : 0 < R)
    (hA : A ∈ Metric.sphere O R)
    (hB : B ∈ Metric.sphere O R)
    (hC : C ∈ Metric.sphere O R)
    (hnBC_unit : ‖nBC‖ = 1)
    (hnBC_perp : inner (𝕜 := by
-- proof
  apply MetaMathlibExt.carnot_inradius_circumradius_general

/--
[carnot_inradius_circumradius](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/CarnotInradius.lean)
-/
@[path]
private lemma carnot_inradius_circumradius_eq
  :
-- imply
  {V : Type*} {P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)]
    (A B C O I : P) (R r x y z : ℝ)
    (nBC nCA nAB : V)
    (hTri : ¬ Collinear ℝ ({A, B, C} : Set P))
    (hRpos : 0 < R)
    (hOplane : O ∈ affineSpan ℝ {A, B, C})
    (hA : A ∈ Metric.sphere O R)
    (hB : B ∈ Metric.sphere O R)
    (hC : C ∈ Metric.sphere O R)
    (hnBC_unit : ‖nBC‖ = 1)
    (hnBC_perp : inner (𝕜 := by
-- proof
  apply MetaMathlibExt.carnot_inradius_circumradius


-- created on 2026-10-20
