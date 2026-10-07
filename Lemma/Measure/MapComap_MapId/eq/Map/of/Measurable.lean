import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Pushing a composition-product along `Prod.map f id` turns a comapped kernel into the original one:
`(ν ⊗ₘ κ.comap f).map (Prod.map f id) = (ν.map f) ⊗ₘ κ`.
-/
@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {ν : Measure α} [SFinite ν]
  {κ : Kernel β γ} [IsSFiniteKernel κ]
  {f : α → β}
-- given
  (hf : Measurable f) :
-- imply
  (ν ⊗ₘ κ.comap f hf).map (Prod.map f id) = (ν.map f) ⊗ₘ κ := by
-- proof
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs, Measure.compProd_apply (hf.prodMap measurable_id hs),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl


-- created on 2026-10-07
