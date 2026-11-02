import Mathlib.Data.EReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Lemma.Real.Sum_Mul_LogDiv.ge.Zero.of.EqSum_1.All_Gt_0.EqSum_1.All_Ge_0
import Initialize.Tactic.Attr.Basic
open Finset Real


private lemma sum_toReal [Fintype α] (μ : PMF α) : ∑ a, (μ a).toReal = 1 := by
  have hsum : ∑ a, μ a = 1 := by
    have htsum : ∑' a, μ a = 1 := μ.tsum_coe
    rwa [← tsum_fintype (L := SummationFilter.unconditional α) (fun a => μ a)]
  rw [← ENNReal.toReal_sum fun a _ => μ.apply_ne_top a, hsum]
  simp

private lemma inf_eq [Fintype α] {μ : PMF α} {I : (α → ℝ) → ENNReal} {A : Set (α → ℝ)} (hμ : ∀ a, 0 < (μ a).toReal) (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / (μ a).toReal))) (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1) → I ν = ⊤) :
  (⨅ ν ∈ A, (I ν : EReal)) = ⨅ ν ∈ {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ A}, toEReal (∑ a, ν a * log (ν a / (μ a).toReal)) := by
  classical
  let kl (ν : α → ℝ) : ℝ := ∑ a, ν a * log (ν a / (μ a).toReal)
  let simplex := {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ A}
  have hsumμ := sum_toReal μ
  apply le_antisymm
  ·
    refine le_iInf₂ ?_
    intro ν hν
    obtain ⟨hge, hsum, hmem⟩ := hν
    have hcoe : (I ν : EReal) = toEReal (kl ν) := by
      rw [hOn ν hge hsum, EReal.coe_ennreal_ofReal, max_eq_left (Sum_Mul_LogDiv.ge.Zero.of.EqSum_1.All_Gt_0.EqSum_1.All_Ge_0 hge hsum hμ hsumμ)]
    rw [← hcoe]
    exact iInf₂_le (f := fun x (_ : x ∈ A) => (I x : EReal)) ν hmem
  ·
    refine le_iInf₂ ?_
    intro ν hνA
    obtain hS | hS := em ((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1)
    ·
      obtain ⟨hge, hsum⟩ := hS
      have hcoe : (I ν : EReal) = toEReal (kl ν) := by
        rw [hOn ν hge hsum, EReal.coe_ennreal_ofReal, max_eq_left (Sum_Mul_LogDiv.ge.Zero.of.EqSum_1.All_Gt_0.EqSum_1.All_Ge_0 hge hsum hμ hsumμ)]
      rw [hcoe]
      exact iInf₂_le (f := fun x (_ : x ∈ simplex) => toEReal (kl x)) ν ⟨hge, hsum, hνA⟩
    ·
      rw [hOut ν hS, EReal.coe_ennreal_top]
      apply le_top

/--
A rate that equals `ENNReal.ofReal` of relative entropy on probability vectors and `⊤` off them
has the same extended infimum, over any set, as that entropy on the probability vectors in the set.
-/
@[path]
private lemma main
  [Fintype α]
  {μ : PMF α}
  {I : (α → ℝ) → ENNReal}
  {A : Set (α → ℝ)}
-- given
  (hμ : ∀ a, 0 < (μ a).toReal)
  (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / (μ a).toReal)))
  (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1) → I ν = ⊤) :
-- imply
  (⨅ ν ∈ A, (I ν : EReal)) =
    ⨅ ν ∈ {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1 ∧ ν ∈ A},
      toEReal (∑ a, ν a * log (ν a / (μ a).toReal)) :=
-- proof
  inf_eq hμ hOn hOut


-- created on 2026-11-02
