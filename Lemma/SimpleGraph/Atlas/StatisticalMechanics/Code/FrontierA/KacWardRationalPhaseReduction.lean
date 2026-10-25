import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalPhaseReduction.Part2
open StatMech StatMech.FrontierA


/--
[dist_vertexLine_lt_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalPhaseReduction.lean)
-/
@[path]
private lemma dist_vertexLine_lt_certificate_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {target : Fin n → ℂ}
  {t : ℝ}
-- given
  (h : KWPolygonPerturbationCertificate polygon)
  (htarget : dist target polygon.vertex < h.radius)
  (ht : t ∈ Icc (0 : ℝ) 1) :
-- imply
  dist (AffineMap.lineMap polygon.vertex target t) polygon.vertex < h.radius := by
-- proof
  apply StatMech.FrontierA.dist_vertexLine_lt_certificate h htarget ht

/--
[KWPolygonPerturbationCertificate.pathPolygon_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalPhaseReduction.lean)
-/
@[path]
private lemma pathPolygon_vertex_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {target : Fin n → ℂ}
  {t : ℝ}
-- given
  (h : KWPolygonPerturbationCertificate polygon)
  (htarget : dist target polygon.vertex < h.radius)
  (ht : t ∈ Icc (0 : ℝ) 1) :
-- imply
  (h.pathPolygon target htarget t).vertex = AffineMap.lineMap polygon.vertex target t := by
-- proof
  apply StatMech.FrontierA.KWPolygonPerturbationCertificate.pathPolygon_vertex h target htarget ht

/--
[KWPolygonPerturbationCertificate.pathPolygon_vertex_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalPhaseReduction.lean)
-/
@[path]
private lemma pathPolygon_vertex_continuous_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {target : Fin n → ℂ}
  {k : Fin n}
-- given
  (h : KWPolygonPerturbationCertificate polygon)
  (htarget : dist target polygon.vertex < h.radius) :
-- imply
  ContinuousOn (fun t : ℝ ↦ (h.pathPolygon target htarget t).vertex k) (Icc 0 1) := by
-- proof
  apply StatMech.FrontierA.KWPolygonPerturbationCertificate.pathPolygon_vertex_continuous h target htarget k

/--
[KWPolygonPerturbationCertificate.pathPolygon_angle_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalPhaseReduction.lean)
-/
@[path]
private lemma pathPolygon_angle_continuous_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {target : Fin n → ℂ}
  {k : Fin n}
-- given
  (h : KWPolygonPerturbationCertificate polygon)
  (htarget : dist target polygon.vertex < h.radius) :
-- imply
  ContinuousOn (fun t : ℝ ↦ (Complex.arg ((h.pathPolygon target htarget t).edgeVector k) : Real.Angle)) (Icc 0 1) := by
-- proof
  apply StatMech.FrontierA.KWPolygonPerturbationCertificate.pathPolygon_angle_continuous h target htarget k

/--
[KWPolygonPerturbationCertificate.phaseCycle_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalPhaseReduction.lean)
-/
@[path]
private lemma phaseCycle_eq_eq
  {n : ℕ}
  [NeZero n]
  {polygon target : KWFiniteSimplePolygon n}
-- given
  (h : KWPolygonPerturbationCertificate polygon)
  (htarget : dist target.vertex polygon.vertex < h.radius) :
-- imply
  kwVectorPhaseCycle polygon.edgeList = kwVectorPhaseCycle target.edgeList := by
-- proof
  apply StatMech.FrontierA.KWPolygonPerturbationCertificate.phaseCycle_eq h htarget

/--
[KWFiniteSimplePolygon.exists_rational_phaseModel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalPhaseReduction.lean)
-/
@[path]
private lemma exists_rational_phaseModel_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ≠ 0) :
-- imply
  ∃ (q : Fin n → ℚ × ℚ) (rational : KWFiniteSimplePolygon n), rational.vertex = kwRatVertex q ∧ kwVectorPhaseCycle polygon.edgeList = kwVectorPhaseCycle rational.edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_rational_phaseModel polygon hcross


-- created on 2026-10-23
