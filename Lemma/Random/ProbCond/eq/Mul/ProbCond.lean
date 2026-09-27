import Mathlib.MeasureTheory.Measure.Count
import Lemma.Measure.EqRnDeriv_Count
import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.PSpace_Joint
import Lemma.Random.PSpace_JointJoint.is.PSpace_Joint_Joint
import Lemma.Random.PSpace_Joint_Joint.of.PSpace_Joint_Joint
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import sympy.stats.joint_rv
open MeasureTheory Measure Random


/--
Discrete chain rule, pointwise at countable atoms:

  `ℙ(x ∧ y | z) = ℙ(x | z) * ℙ(y | x ∧ z)`.

Python: Random.ProbCond.eq.Mul.ProbCond.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  [Countable α] [Countable β] [Countable γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
  [PSpace π (x, y, z)]
-- given
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hβ : ReferenceMeasure.measure (α := β) = Measure.count)
  (hγ : ReferenceMeasure.measure (α := γ) = Measure.count)
  (hx : Measurable x)
  (hy : Measurable y)
  (hz : Measurable z)
  («x.bvar» : α)
  («y.bvar» : β)
  («z.bvar» : γ) :
-- imply
  have : PSpace π ((x, y), z) :=
    PSpace_JointJoint.of.PSpace_Joint_Joint ‹PSpace π (x, y, z)›
  have : PSpace π (x, z) :=
    PSpace_Joint.comm
      (PSpace.of.PSpace_Joint.fst
        (PSpace_JointJoint.of.PSpace_Joint_Joint
          (PSpace_Joint.comm (PSpace_JointJoint.of.PSpace_Joint_Joint
            ‹PSpace π (x, y, z)›))))
  have : PSpace π (y, (x, z)) :=
    PSpace_Joint_Joint.of.PSpace_Joint_Joint ‹PSpace π (x, y, z)›
  have : PSpace π z :=
    PSpace.of.PSpace_Joint.snd ‹PSpace π (x, z)›
  have : ReferenceMeasure.measure (α := α × β) = Measure.count := by
    change (ReferenceMeasure.measure (α := α)).prod
        ReferenceMeasure.measure = Measure.count
    rw [hα, hβ, ← Count.eq.ProdCountS]
  have : ReferenceMeasure.measure (α := (α × β) × γ) = Measure.count := by
    change (ReferenceMeasure.measure (α := α × β)).prod
        ReferenceMeasure.measure = Measure.count
    rw [‹ReferenceMeasure.measure (α := α × β) = Measure.count›, hγ,
      ← Count.eq.ProdCountS (α := α × β)]
  have : ReferenceMeasure.measure (α := α × γ) = Measure.count := by
    change (ReferenceMeasure.measure (α := α)).prod
        ReferenceMeasure.measure = Measure.count
    rw [hα, hγ, ← Count.eq.ProdCountS]
  have : ReferenceMeasure.measure (α := β × (α × γ)) = Measure.count := by
    change (ReferenceMeasure.measure (α := β)).prod
        ReferenceMeasure.measure = Measure.count
    rw [hβ, ‹ReferenceMeasure.measure (α := α × γ) = Measure.count›,
      ← Count.eq.ProdCountS (α := β) (β := α × γ)]
  ℙ[π](x = «x.bvar» ∧ y = «y.bvar» | z = «z.bvar») =
    ℙ[π](x = «x.bvar» | z = «z.bvar») *
      ℙ[π](y = «y.bvar» | x = «x.bvar» ∧ z = «z.bvar») := by
-- proof
  intro _ _ _ _ href_ab href_abg href_ag href_bag
  set sT : Set Ω :=
    {ω | x ω = «x.bvar» ∧ y ω = «y.bvar» ∧ z ω = «z.bvar»} with hsT
  set sB : Set Ω := {ω | x ω = «x.bvar» ∧ z ω = «z.bvar»} with hsB
  set sC : Set Ω := {ω | z ω = «z.bvar»} with hsC
  have hTB : sT ⊆ sB := by
    intro ω hω
    simp only [hsT, hsB, Set.mem_ofPred_eq] at hω ⊢
    exact ⟨hω.1, hω.2.2⟩
  have hBC : sB ⊆ sC := by
    intro ω hω
    simp only [hsB, hsC, Set.mem_ofPred_eq] at hω ⊢
    exact hω.2
  let T : ENNReal := π sT
  let B : ENNReal := π sB
  let C : ENNReal := π sC
  have hxym : AEMeasurable (JointRandomSymbol x y) π :=
    (hx.prodMk hy).aemeasurable
  have hxyzm :
      AEMeasurable (JointRandomSymbol (JointRandomSymbol x y) z) π :=
    hxym.prodMk hz.aemeasurable
  have hxzm : AEMeasurable (JointRandomSymbol x z) π :=
    hx.aemeasurable.prodMk hz.aemeasurable
  have hyxzm :
      AEMeasurable (JointRandomSymbol y (JointRandomSymbol x z)) π :=
    hy.aemeasurable.prodMk hxzm
  have hpreT :
      (JointRandomSymbol (JointRandomSymbol x y) z) ⁻¹'
        {((«x.bvar», «y.bvar»), «z.bvar»)} = sT := by
    ext ω
    simp only [JointRandomSymbol, Set.mem_preimage, Set.mem_singleton_iff,
      hsT, Set.mem_ofPred_eq, Prod.ext_iff, and_assoc]
  have hpreB : (JointRandomSymbol x z) ⁻¹' {(«x.bvar», «z.bvar»)} = sB := by
    ext ω
    simp only [JointRandomSymbol, Set.mem_preimage, Set.mem_singleton_iff,
      hsB, Set.mem_ofPred_eq, Prod.ext_iff]
  have hpreC : z ⁻¹' {«z.bvar»} = sC := by
    ext ω; simp [hsC]
  have hpreT' :
      (JointRandomSymbol y (JointRandomSymbol x z)) ⁻¹'
        {(«y.bvar», («x.bvar», «z.bvar»))} = sT := by
    ext ω
    simp only [JointRandomSymbol, Set.mem_preimage, Set.mem_singleton_iff,
      hsT, Set.mem_ofPred_eq, Prod.ext_iff, and_left_comm]
  have hpreDC : (fun ω ↦ ((JointRandomSymbol (JointRandomSymbol x y) z) ω).2) ⁻¹'
      {«z.bvar»} = sC := by
    ext ω
    simp only [JointRandomSymbol, Set.mem_preimage, Set.mem_singleton_iff,
      hsC, Set.mem_ofPred_eq]
  have hpreDC' : (fun ω ↦ ((JointRandomSymbol x z) ω).2) ⁻¹'
      {«z.bvar»} = sC := by
    ext ω
    simp only [JointRandomSymbol, Set.mem_preimage, Set.mem_singleton_iff,
      hsC, Set.mem_ofPred_eq]
  have hpreBC : (fun ω ↦ ((JointRandomSymbol y (JointRandomSymbol x z)) ω).2) ⁻¹'
      {(«x.bvar», «z.bvar»)} = sB := by
    ext ω
    simp only [JointRandomSymbol, Set.mem_preimage, Set.mem_singleton_iff,
      hsB, Set.mem_ofPred_eq, Prod.ext_iff]
  have hleC : C ≤ 1 := by
    rw [← MeasureTheory.measure_univ (μ := π)]
    exact measure_mono (Set.subset_univ sC)
  have htopC : C ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hleC
  have htopB : B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((measure_mono hBC).trans hleC)
  have htopT : T ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((measure_mono hTB).trans (measure_mono hBC) |>.trans hleC)
  have eq_lhs :
      π.condProb (JointRandomSymbol (JointRandomSymbol x y) z)
        ((«x.bvar», «y.bvar»), «z.bvar») = T / C := by
    unfold Measure.condProb Measure.prob
    rw [href_abg,
      EqRnDeriv_Count (μ := π.map (JointRandomSymbol (JointRandomSymbol x y) z)) _,
      Measure.map_apply_of_aemeasurable hxyzm (measurableSet_singleton _), hpreT,
      hγ,
      EqRnDeriv_Count (μ := π.map (fun ω ↦
        ((JointRandomSymbol (JointRandomSymbol x y) z) ω).2)) _,
      Measure.map_apply_of_aemeasurable hxyzm.snd (measurableSet_singleton _),
      hpreDC]
  have eq_mid : π.condProb (JointRandomSymbol x z) («x.bvar», «z.bvar») = B / C := by
    unfold Measure.condProb Measure.prob
    rw [href_ag, EqRnDeriv_Count (μ := π.map (JointRandomSymbol x z)) _,
      Measure.map_apply_of_aemeasurable hxzm (measurableSet_singleton _), hpreB,
      hγ,
      EqRnDeriv_Count (μ := π.map (fun ω ↦ ((JointRandomSymbol x z) ω).2)) _,
      Measure.map_apply_of_aemeasurable hxzm.snd (measurableSet_singleton _),
      hpreDC']
  have eq_rhs :
      π.condProb (JointRandomSymbol y (JointRandomSymbol x z))
        («y.bvar», («x.bvar», «z.bvar»)) = T / B := by
    unfold Measure.condProb Measure.prob
    rw [href_bag,
      EqRnDeriv_Count (μ := π.map (JointRandomSymbol y (JointRandomSymbol x z))) _,
      Measure.map_apply_of_aemeasurable hyxzm (measurableSet_singleton _), hpreT',
      href_ag,
      EqRnDeriv_Count (μ := π.map (fun ω ↦
        ((JointRandomSymbol y (JointRandomSymbol x z)) ω).2)) _,
      Measure.map_apply_of_aemeasurable hyxzm.snd (measurableSet_singleton _), hpreBC]
  rw [eq_lhs, eq_mid, eq_rhs]
  by_cases hB0 : B = 0
  · have hT0 : T = 0 := measure_mono_null hTB hB0
    rw [hT0, hB0]
    simp
  · have hC0 : C ≠ 0 := fun h ↦ hB0 (measure_mono_null hBC h)
    have : (B / C) * (T / B) = T / C := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      calc
        B * C⁻¹ * (T * B⁻¹)
            = T * (B⁻¹ * B) * C⁻¹ := by ac_rfl
        _ = T * 1 * C⁻¹ := by rw [ENNReal.inv_mul_cancel hB0 htopB]
        _ = T * C⁻¹ := by rw [mul_one]
    exact this.symm


-- created on 2026-09-26
