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
  (hzx : z ⟂ᵢ[π] x | y)
  (hzy : z ⟂ᵢ[π] y) :
-- imply
  z ⟂ᵢ[π] (x, y) := by
-- proof
  have hmzle := mz.comap_le
  have hmyle := my.comap_le
  have hzy_indep :
      Indep (MeasurableSpace.comap z inferInstance) (MeasurableSpace.comap y inferInstance) π :=
    (IndepFun_iff_Indep z y π).1 hzy
  have hzxe := (condIndepFun_iff_condExp_inter_preimage_eq_mul mz mx).1 hzx
  have hrect : ∀ (W : Set γ) (A : Set α) (B : Set β),
      MeasurableSet W → MeasurableSet A → MeasurableSet B →
      π (z ⁻¹' W ∩ (x, y) ⁻¹' (A ×ˢ B)) =
        π (z ⁻¹' W) * π ((x, y) ⁻¹' (A ×ˢ B)) := by
    intro W A B hW hA hB
    set sW : Set Ω := z ⁻¹' W with hsW_def
    set sA : Set Ω := x ⁻¹' A with hsA_def
    set s : Set Ω := sW ∩ sA
    have hsW : MeasurableSet sW := mz hW
    have hsA : MeasurableSet sA := mx hA
    have hs : MeasurableSet s := hsW.inter hsA
    have hpre : sW ∩ (x, y) ⁻¹' (A ×ˢ B) = s ∩ y ⁻¹' B := by
      ext ω; simp [JointRandomSymbol, Set.mem_prod, s, sW, sA, and_assoc]
    have hpreXY : (x, y) ⁻¹' (A ×ˢ B) = sA ∩ y ⁻¹' B := by
      ext ω; simp [JointRandomSymbol, Set.mem_prod, sA]
    have hci :
        π⟦s | MeasurableSpace.comap y inferInstance⟧ =ᵐ[π]
          fun ω ↦ (π⟦sW | MeasurableSpace.comap y inferInstance⟧) ω *
            (π⟦sA | MeasurableSpace.comap y inferInstance⟧) ω :=
      hzxe W A hW hA
    have hWe :
        π⟦sW | MeasurableSpace.comap y inferInstance⟧ =ᵐ[π] fun _ ↦ (π sW).toReal := by
      have h := condExp_indep_eq hmzle hmyle
        ((stronglyMeasurable_const (b := (1 : ℝ))).indicator ⟨W, hW, rfl⟩) hzy_indep
      rw [integral_indicator (mz hW), setIntegral_const, Measure.real_def,
        smul_eq_mul, mul_one] at h
      simpa [hsW_def] using h
    have hprod :
        π⟦s | MeasurableSpace.comap y inferInstance⟧ =ᵐ[π]
          fun ω ↦ (π sW).toReal * (π⟦sA | MeasurableSpace.comap y inferInstance⟧) ω := by
      filter_upwards [hci, hWe] with ω h1 h2
      rw [h1, h2]
    have hiconst : Integrable (fun _ : Ω ↦ (1 : ℝ)) π := integrable_const _
    have hint : Integrable (Set.indicator s fun _ : Ω ↦ (1 : ℝ)) π :=
      hiconst.indicator hs
    have hintA : Integrable (Set.indicator sA fun _ : Ω ↦ (1 : ℝ)) π :=
      hiconst.indicator hsA
    have hrect_real : ∀ (B0 : Set β) (hB0 : MeasurableSet B0),
        (π (s ∩ y ⁻¹' B0)).toReal =
          (π sW).toReal * (π (sA ∩ y ⁻¹' B0)).toReal := by
      intro B0 hB0
      set t0 : Set Ω := y ⁻¹' B0
      have ht0 : MeasurableSet[MeasurableSpace.comap y inferInstance] t0 := ⟨B0, hB0, rfl⟩
      calc
        (π (s ∩ t0)).toReal
            = ∫ ω in s ∩ t0, (1 : ℝ) ∂π := by
              rw [setIntegral_const, Measure.real_def, smul_eq_mul, mul_one]
        _ = ∫ ω, Set.indicator (s ∩ t0) (fun _ : Ω ↦ (1 : ℝ)) ω ∂π :=
              (integral_indicator (hs.inter (my hB0))).symm
        _ = ∫ ω in t0, Set.indicator s (fun _ : Ω ↦ (1 : ℝ)) ω ∂π := by
              rw [Set.inter_comm, ← Set.indicator_indicator, integral_indicator (my hB0)]
        _ = ∫ ω in t0, (π⟦s | MeasurableSpace.comap y inferInstance⟧) ω ∂π :=
              (setIntegral_condExp hmyle hint ht0).symm
        _ = ∫ ω in t0, (fun ω ↦ (π sW).toReal *
              (π⟦sA | MeasurableSpace.comap y inferInstance⟧) ω) ω ∂π :=
              setIntegral_congr_ae (hmyle _ ht0) (hprod.mono fun ω hω _ => hω)
        _ = (π sW).toReal * ∫ ω in t0,
            (π⟦sA | MeasurableSpace.comap y inferInstance⟧) ω ∂π := by
              have hlin :
                  ∫ ω in t0, (fun ω ↦ (π sW).toReal *
                        (π⟦sA | MeasurableSpace.comap y inferInstance⟧) ω) ω ∂π =
                    (π sW).toReal * ∫ ω in t0,
                      (π⟦sA | MeasurableSpace.comap y inferInstance⟧) ω ∂π := by
                rw [← integral_indicator (my hB0), ← integral_indicator (my hB0)]
                have hpt : (fun ω : Ω ↦ Set.indicator t0
                      (fun ω ↦ (π sW).toReal *
                        (π⟦sA | MeasurableSpace.comap y inferInstance⟧) ω) ω) =
                    fun ω ↦ (π sW).toReal * Set.indicator t0
                      (π⟦sA | MeasurableSpace.comap y inferInstance⟧) ω := by
                  funext ω
                  exact Set.indicator_const_mul t0
                    (π⟦sA | MeasurableSpace.comap y inferInstance⟧) (π sW).toReal ω
                rw [hpt, integral_const_mul]
              rw [hlin]
        _ = (π sW).toReal * (π (sA ∩ t0)).toReal := by
              have hf :
                  ∫ ω in t0, (π⟦sA | MeasurableSpace.comap y inferInstance⟧) ω ∂π =
                    (π (sA ∩ t0)).toReal := by
                rw [setIntegral_condExp hmyle hintA ht0]
                rw [← integral_indicator (my hB0), Set.indicator_indicator, Set.inter_comm,
                  integral_indicator (hsA.inter (my hB0))]
                rw [setIntegral_const, Measure.real_def, smul_eq_mul, mul_one]
              rw [hf]
    simp_rw [hpre, hpreXY]
    have hreal :
        (π (s ∩ y ⁻¹' B)).toReal = (π sW * π (sA ∩ y ⁻¹' B)).toReal := by
      rw [ENNReal.toReal_mul]
      exact hrect_real B hB
    have hne1 : π (s ∩ y ⁻¹' B) ≠ ⊤ := measure_ne_top π _
    have hne2 : π sW * π (sA ∩ y ⁻¹' B) ≠ ⊤ :=
      ENNReal.mul_ne_top (measure_ne_top π sW) (measure_ne_top π (sA ∩ y ⁻¹' B))
    refine le_antisymm
      (ENNReal.toReal_le_toReal hne1 hne2 |>.mp hreal.le)
      (ENNReal.toReal_le_toReal hne2 hne1 |>.mp hreal.symm.le)
  have hrect' : ∀ (A : Set α) (B : Set β) (W : Set γ),
      MeasurableSet A → MeasurableSet B → MeasurableSet W →
      π ((x, y) ⁻¹' (A ×ˢ B) ∩ z ⁻¹' W) =
        π ((x, y) ⁻¹' (A ×ˢ B)) * π (z ⁻¹' W) := by
    intro A B W hA hB hW
    have h := hrect W A B hW hA hB
    rw [Set.inter_comm, mul_comm] at h
    exact h
  exact (Random.IndepJoint.of.All_Eq_UFn_MulPreimageS mx my mz hrect').symm


-- created on 2023-04-05
