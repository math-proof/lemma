import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import sympy.stats.joint_rv
import sympy.Basic
open ProbabilityTheory MeasureTheory
open scoped ProbabilityTheory


@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
  [MeasurableSpace γ]
  {π : Measure Ω} [IsFiniteMeasure π]
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
  (h : x ⟂ᵢ[π] (y, z)) :
-- imply
  x ⟂ᵢ[π] y | z := by
-- proof
  refine CondIndepFun.symm ?_
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hx hy hz]
  have h_sym : (fun ω ↦ (y ω, z ω)) ⟂ᵢ[π] x := h.symm
  have h_zy : (fun ω ↦ (z ω, y ω)) ⟂ᵢ[π] x :=
    h_sym.comp measurable_swap measurable_id
  have hxz : x ⟂ᵢ[π] z := h.comp measurable_id measurable_snd
  have h_z_sym : z ⟂ᵢ[π] x := hxz.symm
  have hmap_zyx :
      π.map (fun ω ↦ ((z ω, y ω), x ω)) =
        (π.map (fun ω ↦ (z ω, y ω))).prod (π.map x) :=
    IndepFun.map_prod_eq_prod_map_map (hz.prodMk hy).aemeasurable hx.aemeasurable h_zy
  have hmap_zx :
      π.map (fun ω ↦ (z ω, x ω)) = (π.map z).prod (π.map x) :=
    IndepFun.map_prod_eq_prod_map_map hz.aemeasurable hx.aemeasurable h_z_sym
  have hcd_zy :
      condDistrib x (fun ω ↦ (z ω, y ω)) π
        =ᵐ[π.map (fun ω ↦ (z ω, y ω))] Kernel.const _ (π.map x) := by
    refine (condDistrib_ae_eq_iff_measure_eq_compProd
      (X := fun ω ↦ (z ω, y ω)) hx.aemeasurable (κ := Kernel.const _ (π.map x))).2 ?_
    rw [hmap_zyx, Measure.compProd_const]
  have hcd_z :
      condDistrib x z π =ᵐ[π.map z] Kernel.const _ (π.map x) := by
    refine (condDistrib_ae_eq_iff_measure_eq_compProd
      (X := z) hx.aemeasurable (κ := Kernel.const _ (π.map x))).2 ?_
    rw [hmap_zx, Measure.compProd_const]
  -- Lift `hcd_z` along `Prod.fst` so it lives on `π.map (z,y)`, then take `prodMkRight`.
  have h_right :
      (condDistrib x z π).prodMkRight β
        =ᵐ[π.map (fun ω ↦ (z ω, y ω))] Kernel.const _ (π.map x) := by
    have hfst :
        Measure.map (Prod.fst : γ × β → γ) (π.map (fun ω ↦ (z ω, y ω))) = π.map z := by
      rw [Measure.map_map measurable_fst (hz.prodMk hy)]
      rfl
    -- Lift a.e. equality along `Prod.fst : map(z,y) → map z`.
    have htendsto :
        Filter.Tendsto (Prod.fst : γ × β → γ)
          (ae (π.map (fun ω ↦ (z ω, y ω)))) (ae (π.map z)) := by
      simpa [hfst] using
        Measure.tendsto_ae_map (μ := π.map (fun ω ↦ (z ω, y ω))) measurable_fst.aemeasurable
    have hcd' :
        (⇑(condDistrib x z π)) =ᶠ[ae (π.map z)] (⇑(Kernel.const γ (π.map x))) :=
      hcd_z
    have hcomp :
        (fun p : γ × β ↦ (condDistrib x z π) p.1)
          =ᶠ[ae (π.map (fun ω ↦ (z ω, y ω)))]
        (fun p ↦ (Kernel.const γ (π.map x)) p.1) :=
      hcd'.comp_tendsto htendsto
    filter_upwards [hcomp] with p hp
    -- `prodMkRight κ (c,b) = κ c` and `Kernel.const (c,b) = π.map x`
    simpa [Kernel.prodMkRight_apply, Kernel.const_apply] using hp
  -- Both sides equal the same constant kernel a.e.
  filter_upwards [hcd_zy, h_right] with p hL hR
  rw [hL, hR]


-- created on 2026-09-21
