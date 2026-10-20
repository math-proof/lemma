import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Integral.PrekopaLeindler
open MeasureTheory
open scoped ENNReal
open MathlibExt.MeasureTheory.Integral.PrekopaLeindlerWanted


/--
[prekopa_leindler](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Integral/PrekopaLeindler.lean)
-/
@[path]
private lemma prekopa_leindler_eq
  {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))] [BorelSpace (EuclideanSpace ℝ (Fin n))]
  {t : ℝ}
  {f g h : EuclideanSpace ℝ (Fin n) → ENNReal}
-- given
  (ht0 : 0 < t)
  (ht1 : t < 1)
  (hf : Measurable f)
  (hg : Measurable g)
  (hh : Measurable h)
  (hfgh : ∀ x y : EuclideanSpace ℝ (Fin n), ENNReal.rpow (f x) (1 - t) * ENNReal.rpow (g y) t ≤ h ((1 - t) • x + t • y)) :
-- imply
  ENNReal.rpow (∫⁻ x, f x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) (1 - t) *
    ENNReal.rpow (∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) t ≤
    ∫⁻ x, h x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
-- proof
  apply MathlibExt.MeasureTheory.Integral.PrekopaLeindlerWanted.prekopa_leindler ht0 ht1 hf hg hh hfgh


-- created on 2026-10-20
