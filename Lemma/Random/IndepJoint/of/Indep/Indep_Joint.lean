import Mathlib.Probability.Independence.Basic
import sympy.stats.joint_rv
import sympy.Basic
open ProbabilityTheory MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
  [PSpace 𝕡 x] [PSpace 𝕡 y] [PSpace 𝕡 z]
-- given
  (hx : x ⟂ᵢ[𝕡] z)
  (hy : y ⟂ᵢ[𝕡] (x, z)) :
-- imply
  (x, y) ⟂ᵢ[𝕡] z := by
-- proof
  have hx_m : AEMeasurable x 𝕡 := PSpace.aemeasurable
  have hy_m : AEMeasurable y 𝕡 := PSpace.aemeasurable
  have hz_m : AEMeasurable z 𝕡 := PSpace.aemeasurable
  have hxz_m : AEMeasurable (x, z) 𝕡 := hx_m.prodMk hz_m
  have hxy_m : AEMeasurable (x, y) 𝕡 := hx_m.prodMk hy_m
  have hyxz_m : AEMeasurable (y, (x, z)) 𝕡 := hy_m.prodMk hxz_m
  -- `y ⊥ (x, z)` ⇒ `y ⊥ x` ⇒ `x ⊥ y`
  have hxy : x ⟂ᵢ[𝕡] y := (hy.comp measurable_id measurable_fst).symm
  -- `(b, (a, c)) ↦ ((a, b), c)`
  let e : β × (α × γ) ≃ᵐ (α × β) × γ :=
    MeasurableEquiv.prodAssoc.symm.trans
      (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ))
  have h_comp : ((x, y), z) = ⇑e ∘ (y, (x, z)) := by
    funext ω; rfl
  have hassoc (μ : Measure α) (ν : Measure β) (ξ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ξ] :
      Measure.map e (ν.prod (μ.prod ξ)) = (μ.prod ν).prod ξ := by
    have h1 :
        Measure.map MeasurableEquiv.prodAssoc.symm (ν.prod (μ.prod ξ)) =
          (ν.prod μ).prod ξ := by
      have h :
          Measure.map MeasurableEquiv.prodAssoc ((ν.prod μ).prod ξ) =
            ν.prod (μ.prod ξ) := Measure.prodAssoc_prod
      have := congrArg (Measure.map MeasurableEquiv.prodAssoc.symm) h
      simpa [Measure.map_map, Measure.map_id, MeasurableEquiv.self_comp_symm] using
        this.symm
    have h2 :
        Measure.map
            (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ))
            ((ν.prod μ).prod ξ) =
          (μ.prod ν).prod ξ := by
      have hfun :
          (⇑(MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ)) :
              (β × α) × γ → (α × β) × γ) =
            Prod.map Prod.swap (id : γ → γ) := by
        funext ⟨⟨b, a⟩, c⟩
        rfl
      rw [hfun, ← Measure.map_prod_map _ _ measurable_swap measurable_id, Measure.prod_swap,
        Measure.map_id]
    calc
      Measure.map e (ν.prod (μ.prod ξ))
          = Measure.map
              (⇑(MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ)) ∘
                ⇑MeasurableEquiv.prodAssoc.symm)
              (ν.prod (μ.prod ξ)) := by rfl
      _ = Measure.map
              (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ))
              (Measure.map MeasurableEquiv.prodAssoc.symm (ν.prod (μ.prod ξ))) := by
            rw [Measure.map_map
              (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm
                (MeasurableEquiv.refl γ)).measurable
              MeasurableEquiv.prodAssoc.symm.measurable]
      _ = Measure.map
              (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ))
              ((ν.prod μ).prod ξ) := by rw [h1]
      _ = (μ.prod ν).prod ξ := h2
  have hy_law :
      𝕡.map (y, (x, z)) = (𝕡.map y).prod (𝕡.map (x, z)) :=
    IndepFun.map_prod_eq_prod_map_map hy_m hxz_m hy
  have hx_law :
      𝕡.map (x, z) = (𝕡.map x).prod (𝕡.map z) :=
    IndepFun.map_prod_eq_prod_map_map hx_m hz_m hx
  have hxy_law :
      𝕡.map (x, y) = (𝕡.map x).prod (𝕡.map y) :=
    IndepFun.map_prod_eq_prod_map_map hx_m hy_m hxy
  rw [indepFun_iff_map_prod_eq_prod_map_map hxy_m hz_m]
  have hmap :
      𝕡.map ((x, y), z) = Measure.map e (𝕡.map (y, (x, z))) := by
    rw [h_comp]
    exact (AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hyxz_m).symm
  calc
    _ = 𝕡.map ((x, y), z) := rfl
    _ = Measure.map e (𝕡.map (y, (x, z))) := hmap
    _ = Measure.map e ((𝕡.map y).prod (𝕡.map (x, z))) := by rw [hy_law]
    _ = Measure.map e ((𝕡.map y).prod ((𝕡.map x).prod (𝕡.map z))) := by rw [hx_law]
    _ = ((𝕡.map x).prod (𝕡.map y)).prod (𝕡.map z) := hassoc _ _ _
    _ = (𝕡.map (x, y)).prod (𝕡.map z) := by rw [← hxy_law]


-- created on 2026-09-19
