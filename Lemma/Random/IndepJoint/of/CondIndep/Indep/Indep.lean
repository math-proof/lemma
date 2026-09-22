import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Conditional
import sympy.stats.joint_rv
import Lemma.Random.IndepJoint.of.All_Eq_UFn_MulPreimageS
open ProbabilityTheory MeasureTheory
open scoped ProbabilityTheory ENNReal


@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (mx : Measurable x) (my : Measurable y) (mz : Measurable z)
  (hx : x ⟂ᵢ[π] z)
  (hy : y ⟂ᵢ[π] z)
  (hCI : x ⟂ᵢ[π] y | z) :
-- imply
  (x, y) ⟂ᵢ[π] z := by
-- proof
  have hmz := mz.comap_le
  have hmxle := mx.comap_le
  have hmyle := my.comap_le
  have hx_indep :
      Indep (MeasurableSpace.comap x inferInstance) (MeasurableSpace.comap z inferInstance) π :=
    (IndepFun_iff_Indep x z π).1 hx
  have hy_indep :
      Indep (MeasurableSpace.comap y inferInstance) (MeasurableSpace.comap z inferInstance) π :=
    (IndepFun_iff_Indep y z π).1 hy
  have hCIe := (condIndepFun_iff_condExp_inter_preimage_eq_mul mx my).1 hCI
  have hrect : ∀ (A : Set α) (B : Set β) (V : Set γ),
      MeasurableSet A → MeasurableSet B → MeasurableSet V →
      π ((x, y) ⁻¹' (A ×ˢ B) ∩ z ⁻¹' V) =
        π ((x, y) ⁻¹' (A ×ˢ B)) * π (z ⁻¹' V) := by
    intro A B V hA hB hV
    set sA : Set Ω := x ⁻¹' A with hsA_def
    set sB : Set Ω := y ⁻¹' B with hsB_def
    set s : Set Ω := sA ∩ sB
    have hsA : MeasurableSet sA := mx hA
    have hsB : MeasurableSet sB := my hB
    have hs : MeasurableSet s := hsA.inter hsB
    have hpreXY : (x, y) ⁻¹' (A ×ˢ B) = s := by
      ext ω; simp [JointRandomSymbol, Set.mem_prod, s, sA, sB]
    have hci :
        π⟦s | MeasurableSpace.comap z inferInstance⟧ =ᵐ[π]
          fun ω ↦ (π⟦sA | MeasurableSpace.comap z inferInstance⟧) ω *
            (π⟦sB | MeasurableSpace.comap z inferInstance⟧) ω :=
      hCIe A B hA hB
    have hAe :
        π⟦sA | MeasurableSpace.comap z inferInstance⟧ =ᵐ[π] fun _ ↦ (π sA).toReal := by
      have h := condExp_indep_eq hmxle hmz
        ((stronglyMeasurable_const (b := (1 : ℝ))).indicator ⟨A, hA, rfl⟩) hx_indep
      rw [integral_indicator (mx hA), setIntegral_const, Measure.real_def,
        smul_eq_mul, mul_one] at h
      simpa [hsA_def] using h
    have hBe :
        π⟦sB | MeasurableSpace.comap z inferInstance⟧ =ᵐ[π] fun _ ↦ (π sB).toReal := by
      have h := condExp_indep_eq hmyle hmz
        ((stronglyMeasurable_const (b := (1 : ℝ))).indicator ⟨B, hB, rfl⟩) hy_indep
      rw [integral_indicator (my hB), setIntegral_const, Measure.real_def,
        smul_eq_mul, mul_one] at h
      simpa [hsB_def] using h
    have hconst :
        π⟦s | MeasurableSpace.comap z inferInstance⟧ =ᵐ[π]
          fun _ ↦ (π sA).toReal * (π sB).toReal := by
      filter_upwards [hci, hAe, hBe] with ω h1 h2 h3
      rw [h1, h2, h3]
    have hiconst : Integrable (fun _ : Ω ↦ (1 : ℝ)) π := integrable_const _
    have hint : Integrable (Set.indicator s fun _ : Ω ↦ (1 : ℝ)) π :=
      hiconst.indicator hs
    have hrect_real : ∀ (V0 : Set γ) (hV0 : MeasurableSet V0),
        (π (s ∩ z ⁻¹' V0)).toReal =
          (π sA).toReal * (π sB).toReal * (π (z ⁻¹' V0)).toReal := by
      intro V0 hV0
      set t0 : Set Ω := z ⁻¹' V0
      have ht0 : MeasurableSet[MeasurableSpace.comap z inferInstance] t0 := ⟨V0, hV0, rfl⟩
      calc
        (π (s ∩ t0)).toReal
            = ∫ ω in s ∩ t0, (1 : ℝ) ∂π := by
              rw [setIntegral_const, Measure.real_def, smul_eq_mul, mul_one]
        _ = ∫ ω, Set.indicator (s ∩ t0) (fun _ : Ω ↦ (1 : ℝ)) ω ∂π :=
              (integral_indicator (hs.inter (mz hV0))).symm
        _ = ∫ ω in t0, Set.indicator s (fun _ : Ω ↦ (1 : ℝ)) ω ∂π := by
              rw [Set.inter_comm, ← Set.indicator_indicator, integral_indicator (mz hV0)]
        _ = ∫ ω in t0, (π⟦s | MeasurableSpace.comap z inferInstance⟧) ω ∂π :=
              (setIntegral_condExp hmz hint ht0).symm
        _ = ∫ ω in t0, (fun _ ↦ (π sA).toReal * (π sB).toReal) ω ∂π :=
              setIntegral_congr_ae (hmz _ ht0) (hconst.mono fun ω hω _ => hω)
        _ = (π t0).toReal * ((π sA).toReal * (π sB).toReal) := by
              rw [setIntegral_const, Measure.real_def, smul_eq_mul]
        _ = (π sA).toReal * (π sB).toReal * (π t0).toReal := by ring
    have h_marg : (π s).toReal = (π sA).toReal * (π sB).toReal := by
      have h := hrect_real Set.univ MeasurableSet.univ
      simpa using h
    simp_rw [hpreXY]
    have hreal :
        (π (s ∩ z ⁻¹' V)).toReal = (π s * π (z ⁻¹' V)).toReal := by
      rw [ENNReal.toReal_mul, h_marg]
      exact hrect_real V hV
    have hne1 : π (s ∩ z ⁻¹' V) ≠ ⊤ := measure_ne_top π _
    have hne2 : π s * π (z ⁻¹' V) ≠ ⊤ :=
      ENNReal.mul_ne_top (measure_ne_top π s) (measure_ne_top π (z ⁻¹' V))
    refine le_antisymm
      (ENNReal.toReal_le_toReal hne1 hne2 |>.mp hreal.le)
      (ENNReal.toReal_le_toReal hne2 hne1 |>.mp hreal.symm.le)
  exact Random.IndepJoint.of.All_Eq_UFn_MulPreimageS mx my mz hrect


-- created on 2026-09-22
