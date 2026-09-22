import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import sympy.stats.joint_rv
import Lemma.Random.IndepJoint.of.All_Eq_UFn_MulPreimageS
open ProbabilityTheory MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (mx : Measurable x) (my : Measurable y) (mz : Measurable z)
  (hx : x ⟂ᵢ[π] (y, z))
  (hy : y ⟂ᵢ[π] z) :
-- imply
  (x, y) ⟂ᵢ[π] z := by
-- proof
  have hx_iff := (IndepFun_iff x (y, z) π).1 hx
  have hy_iff := (IndepFun_iff y z π).1 hy
  have hrect : ∀ (A : Set α) (B : Set β) (V : Set γ),
      MeasurableSet A → MeasurableSet B → MeasurableSet V →
      π ((x, y) ⁻¹' (A ×ˢ B) ∩ z ⁻¹' V) =
        π ((x, y) ⁻¹' (A ×ˢ B)) * π (z ⁻¹' V) := by
    intro A B V hA hB hV
    have hBC : MeasurableSet (B ×ˢ V) := hB.prod hV
    have hBuniv : MeasurableSet (B ×ˢ (Set.univ : Set γ)) := hB.prod MeasurableSet.univ
    have hpre : (y, z) ⁻¹' (B ×ˢ V) = y ⁻¹' B ∩ z ⁻¹' V := by
      ext ω; simp [JointRandomSymbol, Set.mem_prod]
    have h_left :=
      hx_iff (x ⁻¹' A) ((y, z) ⁻¹' (B ×ˢ V))
        ⟨A, hA, rfl⟩ ⟨B ×ˢ V, hBC, rfl⟩
    rw [hpre] at h_left
    have h_yz := hy_iff (y ⁻¹' B) (z ⁻¹' V) ⟨B, hB, rfl⟩ ⟨V, hV, rfl⟩
    have hpreU : (y, z) ⁻¹' (B ×ˢ (Set.univ : Set γ)) = y ⁻¹' B := by
      ext ω; simp [JointRandomSymbol, Set.mem_prod]
    have h_marg :=
      hx_iff (x ⁻¹' A) ((y, z) ⁻¹' (B ×ˢ Set.univ))
        ⟨A, hA, rfl⟩ ⟨B ×ˢ Set.univ, hBuniv, rfl⟩
    rw [hpreU] at h_marg
    have hpreXY : (x, y) ⁻¹' (A ×ˢ B) = x ⁻¹' A ∩ y ⁻¹' B := by
      ext ω; simp [JointRandomSymbol, Set.mem_prod]
    simp_rw [hpreXY]
    calc
      π (x ⁻¹' A ∩ y ⁻¹' B ∩ z ⁻¹' V)
          = π (x ⁻¹' A ∩ (y ⁻¹' B ∩ z ⁻¹' V)) := by rw [Set.inter_assoc]
      _ = π (x ⁻¹' A) * π (y ⁻¹' B ∩ z ⁻¹' V) := h_left
      _ = π (x ⁻¹' A) * (π (y ⁻¹' B) * π (z ⁻¹' V)) := by rw [h_yz]
      _ = (π (x ⁻¹' A) * π (y ⁻¹' B)) * π (z ⁻¹' V) := by ring
      _ = π (x ⁻¹' A ∩ y ⁻¹' B) * π (z ⁻¹' V) := by rw [← h_marg]
  exact Random.IndepJoint.of.All_Eq_UFn_MulPreimageS mx my mz hrect


-- created on 2026-09-22
