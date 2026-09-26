import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω}
  {a : Ω → α} [PSpace π a]
  {f g : α → EReal}
-- given
  (h₀ : f ≥ g) :
-- imply
  𝔼[a: π](f a) ≥ 𝔼[a: π](g a) := by
-- proof
  simp only [Expectation.ofRV]
  apply EReal.sub_le_sub
  · exact_mod_cast lintegral_mono fun x => EReal.toENNReal_le_toENNReal (h₀ x)
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (lintegral_mono (μ := π.map a) fun x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (h₀ x)))


-- created on 2026-09-26
