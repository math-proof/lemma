import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace HaarQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

def weight (H : Subgroup G) (μH : Measure H) : G → ℝ≥0∞ :=
  open Classical in
  if h : SigmaCompactSpace G ∧ WeaklyLocallyCompactSpace G then
    haveI := h.1
    haveI := h.2
    fun g => ∑' n : ℕ,
      (2⁻¹ : ℝ≥0∞) ^ n *
        (1 + μH (((↑) : H → G) ⁻¹'
          ((CompactExhaustion.choice G (n + 1) : Set G) *
            (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹ *
        (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g
  else 0

def density (H : Subgroup G) (μH : Measure H) (g : G) : ℝ≥0∞ :=
  weight H μH g / ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH

def measure (μ : Measure G) (H : Subgroup G) (μH : Measure H) :
    Measure (MulAction.orbitRel.Quotient H G) :=
  Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
    (μ.withDensity (density H μH))

end HaarQuotient

end
