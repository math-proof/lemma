import sympy.stats.markov_samples
import sympy.Basic
import Lemma.Anchors.RobbinsMonroβ
import Lemma.Real.Any_And_Ge_0_All_Le.of.Summable
import Lemma.Skeleton.Any_Ge_0AndAll_All_LeNormSub_MulNormSub
import Lemma.Iterates.Any_Ge_0AndAll_All_LeNormSub_MulSumIco_Exp.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.All_Ge_0.IteratesOfResidual
open Finset Real Iterates


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {sk : Skeleton S d} :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ ω n, ‖sk.e₂₁ (n + 1) ω‖ ≤ C * sk.anc.β n ^ 2 * (‖sk.x (sk.anc.t n) ω‖ + 1) := by
-- proof
  have hα : RobbinsMonro sk.α := sk.anc.hα
  have hβ : RobbinsMonro sk.anc.β := Anchors.RobbinsMonroβ
  obtain ⟨C₁, hC₁, hβC⟩ := Any_And_Ge_0_All_Le.of.Summable hβ.sqsum
  obtain ⟨C₂, hC₂, hgrowth⟩ := Any_Ge_0AndAll_All_LeNormSub_MulSumIco_Exp.of.Any_Ge_0AndAll_All_LeNormSub_MulNormSub.All_Ge_0.IteratesOfResidual sk.hx (fun n => (hα.pos n).le) sk.hFlip
  obtain ⟨C₃, hC₃, hG⟩ := Skeleton.Any_Ge_0AndAll_All_LeNormSub_MulNormSub (sk := sk)
  refine ⟨C₃ * C₂ * rexp (C₁ * C₂), by positivity, fun ω n => ?_⟩
  have hβn := hβ.pos n
  have key : ∀ i ∈ Ico (sk.anc.t n) (sk.anc.t (n + 1)), ‖sk.α i • (sk.G (sk.x i ω) (ω (i + 1)) - sk.G (sk.x (sk.anc.t n) ω) (ω (i + 1)))‖ ≤
      sk.α i * (C₃ * (sk.anc.β n * C₂ * (‖sk.x (sk.anc.t n) ω‖ + 1) * rexp (sk.anc.β n * C₂))) := fun i hi => by
    have hαi := hα.pos i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hαi]
    gcongr
    refine (hG _ _ _).trans ?_
    gcongr
    simpa only [← sum_mul, Anchors.β] using hgrowth ω _ _ i hi
  simp only [Skeleton.e₂₁, Nat.add_sub_cancel]
  calc _ ≤ _ := norm_sum_le _ _
    _ ≤ _ := sum_le_sum key
    _ = sk.anc.β n * (C₃ * (sk.anc.β n * C₂ * (‖sk.x (sk.anc.t n) ω‖ + 1) * rexp (sk.anc.β n * C₂))) := by rw [← sum_mul]; rfl
    _ = C₃ * C₂ * sk.anc.β n ^ 2 * (‖sk.x (sk.anc.t n) ω‖ + 1) * rexp (sk.anc.β n * C₂) := by ring
    _ ≤ C₃ * C₂ * sk.anc.β n ^ 2 * (‖sk.x (sk.anc.t n) ω‖ + 1) * rexp (C₁ * C₂) := by gcongr; exact hβC n
    _ = _ := by ring


-- created on 2026-09-26