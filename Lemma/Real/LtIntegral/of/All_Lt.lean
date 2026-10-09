import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import sympy.integrals.integrals
import sympy.sets.sets
import sympy.Basic


open MeasureTheory


@[path]
private lemma main
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : f ∈ ℒ¹ a b)
  (hgi : g ∈ ℒ¹ a b)
  (h : ∀ x ∈ Set.Ioo a b, f x < g x) :
-- imply
  ∫ x : ℝ in a..b, f x < ∫ x : ℝ in a..b, g x := by
-- proof
  have hbn : ∀ᵐ (x : ℝ) ∂volume, x ≠ b := Measure.ae_ne volume b
  have hae : f ≤ᵐ[volume.restrict (Set.Ioc a b)] g :=
    (ae_restrict_iff' measurableSet_Ioc).mpr <| by
      filter_upwards [hbn] with x hxb hx
      have hxo : x ∈ Set.Ioo a b :=
        ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩
      exact (h x hxo).le
  have hpos : 0 < volume (Set.Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hsub : Set.Ioo a b ⊆ Set.Ioc a b := fun x hx =>
    ⟨hx.1, hx.2.le⟩
  have hI : (volume.restrict (Set.Ioc a b)) (Set.Ioo a b) = volume (Set.Ioo a b) := by
    rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_self_of_subset_left hsub]
  have hv : 0 < (volume.restrict (Set.Ioc a b)) {x | f x < g x} :=
    calc
      0 < volume (Set.Ioo a b) := hpos
      _ = (volume.restrict (Set.Ioc a b)) (Set.Ioo a b) := hI.symm
      _ ≤ (volume.restrict (Set.Ioc a b)) {x | f x < g x} :=
        measure_mono fun x hx => h x hx
  exact intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero
    hab.le hfi hgi hae hv.ne'


-- created on 2019-01-29
