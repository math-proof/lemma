/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Order.LeftRightNhds
import Def.Analysis.Complex.LoomanMenchoff.Part4
/-!
# The Looman–Menchoff theorem

This file proves that a continuous complex-valued function with everywhere-existing partial
derivatives satisfying the Cauchy–Riemann equations is complex differentiable.
-/


namespace MetaMathlibExt

open Set Filter MeasureTheory Metric Finset

open BoxIntegral

open scoped ENNReal Interval NNReal Topology BoxIntegral Matrix

noncomputable section

theorem looman_isOpen_holomorphicNeighborhood {s : Set ℂ} {f : ℂ → ℂ} :
    IsOpen (loomanHolomorphicNeighborhood s f) := by
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨t, ht, hzt, hts, hdiff⟩
  exact ⟨t, fun w hw ↦ ⟨t, ht, hw, hts, hdiff⟩, ht, hzt⟩

theorem looman_differentiableAt_of_mem_holomorphicNeighborhood
    {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ loomanHolomorphicNeighborhood s f) : DifferentiableAt ℂ f z := by
  rcases hz with ⟨t, ht, hzt, -, hdiff⟩
  exact (hdiff z hzt).differentiableAt (ht.mem_nhds hzt)

theorem looman_abs_deriv_re_le_of_norm_sub_le {g : ℝ → ℂ} {a K : ℝ}
    (hg : HasDerivAt (fun t ↦ (g t).re) a 0) (hK : 0 ≤ K)
    (hlip : ∀ᶠ t in nhds 0, ‖g t - g 0‖ ≤ K * ‖t‖) : |a| ≤ K := by
  rw [← Real.norm_eq_abs]
  apply hg.le_of_lip' hK
  filter_upwards [hlip] with t ht
  calc
    ‖(g t).re - (g 0).re‖ = |(g t - g 0).re| := by simp [Real.norm_eq_abs]
    _ ≤ ‖g t - g 0‖ := Complex.abs_re_le_norm _
    _ ≤ K * ‖t - 0‖ := by simpa using ht

theorem looman_abs_deriv_im_le_of_norm_sub_le {g : ℝ → ℂ} {a K : ℝ}
    (hg : HasDerivAt (fun t ↦ (g t).im) a 0) (hK : 0 ≤ K)
    (hlip : ∀ᶠ t in nhds 0, ‖g t - g 0‖ ≤ K * ‖t‖) : |a| ≤ K := by
  rw [← Real.norm_eq_abs]
  apply hg.le_of_lip' hK
  filter_upwards [hlip] with t ht
  calc
    ‖(g t).im - (g 0).im‖ = |(g t - g 0).im| := by simp [Real.norm_eq_abs]
    _ ≤ ‖g t - g 0‖ := Complex.abs_im_le_norm _
    _ ≤ K * ‖t - 0‖ := by simpa using ht

end
end MetaMathlibExt
