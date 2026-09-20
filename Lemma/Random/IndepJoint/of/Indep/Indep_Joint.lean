import Mathlib.Probability.Independence.Basic
import sympy.stats.joint_rv
import sympy.Basic
open ProbabilityTheory MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
  [PSpace π x] [PSpace π y] [PSpace π z]
-- given
  (hx : x ⟂ᵢ[π] z)
  (hy : y ⟂ᵢ[π] (x, z)) :
-- imply
  (x, y) ⟂ᵢ[π] z := by
-- proof
  have hx_m : AEMeasurable x π := PSpace.aemeasurable
  have hy_m : AEMeasurable y π := PSpace.aemeasurable
  have hz_m : AEMeasurable z π := PSpace.aemeasurable
  have hxz_m : AEMeasurable (x, z) π := hx_m.prodMk hz_m
  have hxy_m : AEMeasurable (x, y) π := hx_m.prodMk hy_m
  have hyxz_m : AEMeasurable (y, (x, z)) π := hy_m.prodMk hxz_m
  -- `y ⊥ (x, z)` ⇒ `y ⊥ x` ⇒ `x ⊥ y`
  have hxy : x ⟂ᵢ[π] y := (hy.comp measurable_id measurable_fst).symm
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
      π.map (y, (x, z)) = (π.map y).prod (π.map (x, z)) :=
    IndepFun.map_prod_eq_prod_map_map hy_m hxz_m hy
  have hx_law :
      π.map (x, z) = (π.map x).prod (π.map z) :=
    IndepFun.map_prod_eq_prod_map_map hx_m hz_m hx
  have hxy_law :
      π.map (x, y) = (π.map x).prod (π.map y) :=
    IndepFun.map_prod_eq_prod_map_map hx_m hy_m hxy
  rw [indepFun_iff_map_prod_eq_prod_map_map hxy_m hz_m]
  have hmap :
      π.map ((x, y), z) = Measure.map e (π.map (y, (x, z))) := by
    rw [h_comp]
    exact (AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hyxz_m).symm
  calc
    _ = π.map ((x, y), z) := rfl
    _ = Measure.map e (π.map (y, (x, z))) := hmap
    _ = Measure.map e ((π.map y).prod (π.map (x, z))) := by rw [hy_law]
    _ = Measure.map e ((π.map y).prod ((π.map x).prod (π.map z))) := by rw [hx_law]
    _ = ((π.map x).prod (π.map y)).prod (π.map z) := hassoc _ _ _
    _ = (π.map (x, y)).prod (π.map z) := by rw [← hxy_law]


-- created on 2023-04-01
