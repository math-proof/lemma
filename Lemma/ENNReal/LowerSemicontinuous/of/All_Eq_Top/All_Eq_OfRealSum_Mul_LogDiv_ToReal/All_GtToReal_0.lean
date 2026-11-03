import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Semicontinuity.Basic
import Initialize.Tactic.Attr.Basic
open Finset Real Set


private lemma continuous_entropy {m : ℝ} (hm : 0 < m) : Continuous fun t : ℝ => t * log (t / m) := by
  have hfun : (fun t : ℝ => t * log (t / m)) = fun t => t * log t - t * log m := by
    ext t
    obtain rfl | ht := eq_or_ne t 0
    · simp
    · rw [log_div ht hm.ne', mul_sub]
  rw [hfun]
  exact continuous_mul_log.sub (continuous_id.mul continuous_const)

private lemma continuous_kl [Fintype α] {m : α → ℝ} (hm : ∀ a, 0 < m a) : Continuous fun ν : α → ℝ => ∑ a, ν a * log (ν a / m a) := by
  refine continuous_finsetSum univ ?_
  intro a _
  exact (continuous_entropy (hm a)).comp (continuous_apply a)

private lemma isClosed_simplex [Fintype α] : IsClosed {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1} := by
  have horth : IsClosed {ν : α → ℝ | ∀ a, 0 ≤ ν a} := by
    have hpi : {ν : α → ℝ | ∀ a, 0 ≤ ν a} = Set.pi univ (fun _ => Set.Ici 0) := by
      ext ν
      simp [Set.mem_Ici, Pi.le_def]
    rw [hpi]
    exact isClosed_set_pi fun _ _ => isClosed_Ici
  have hsum : IsClosed {ν : α → ℝ | ∑ a, ν a = 1} := by
    have hcont : Continuous fun ν : α → ℝ => ∑ a, ν a := by
      refine continuous_finsetSum univ ?_
      intro a _
      exact continuous_apply a
    have hpre : {ν : α → ℝ | ∑ a, ν a = 1} = (fun ν : α → ℝ => ∑ a, ν a) ⁻¹' {1} := by
      ext ν
      simp
    rw [hpre]
    exact isClosed_singleton.preimage hcont
  have hinter : {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1} = {ν : α → ℝ | ∀ a, 0 ≤ ν a} ∩ {ν : α → ℝ | ∑ a, ν a = 1} := by
    ext ν
    simp
  rw [hinter]
  exact horth.inter hsum

private lemma lowerSemicontinuous_rate [Fintype α] {μ : PMF α} {I : (α → ℝ) → ENNReal} (hμ : ∀ a, 0 < (μ a).toReal) (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / (μ a).toReal))) (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1) → I ν = ⊤) :
  LowerSemicontinuous I := by
  classical
  let S := {ν : α → ℝ | (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1}
  let kl (ν : α → ℝ) : ℝ := ∑ a, ν a * log (ν a / (μ a).toReal)
  rw [lowerSemicontinuous_iff_frequently]
  intro x y hfreq
  obtain rfl | hy := em (y = ⊤)
  · apply le_top
  ·
    obtain hx | hx := em (x ∈ S)
    ·
      obtain ⟨hge, hsum⟩ := hx
      have hfreqR : ∃ᶠ x' in nhds x, kl x' ≤ ENNReal.toReal y := by
        refine hfreq.mono ?_
        intro x' hIx'
        have hx' : x' ∈ S := by
          obtain hx' | hx' := em (x' ∈ S)
          · exact hx'
          · exact absurd (top_le_iff.mp ((hOut x' hx') ▸ hIx')) hy
        obtain ⟨hge', hsum'⟩ := hx'
        rw [hOn x' hge' hsum'] at hIx'
        exact (ENNReal.ofReal_le_iff_le_toReal hy).mp hIx'
      have hle := (continuous_kl hμ).lowerSemicontinuous.frequently x (ENNReal.toReal y) hfreqR
      rw [hOn x hge hsum]
      simpa [kl] using (ENNReal.ofReal_le_iff_le_toReal hy).mpr hle
    ·
      exfalso
      have hmem : x ∈ closure S := by
        refine Filter.Frequently.mem_closure ?_
        refine hfreq.mono ?_
        intro x' hIx'
        obtain hx' | hx' := em (x' ∈ S)
        · exact hx'
        · exact absurd (top_le_iff.mp ((hOut x' hx') ▸ hIx')) hy
      have hclosed : IsClosed S := isClosed_simplex
      rw [hclosed.closure_eq] at hmem
      exact hx hmem

/--
When every reference mass is positive, a rate that equals `ENNReal.ofReal` of relative entropy on
probability vectors and `⊤` off them is lower semicontinuous.
-/
@[path]
private lemma main
  [Fintype α]
  {μ : PMF α}
  {I : (α → ℝ) → ENNReal}
-- given
  (hμ : ∀ a, 0 < (μ a).toReal)
  (hOn : ∀ ν, (∀ a, 0 ≤ ν a) → ∑ a, ν a = 1 → I ν = ENNReal.ofReal (∑ a, ν a * log (ν a / (μ a).toReal)))
  (hOut : ∀ ν, ¬((∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1) → I ν = ⊤) :
-- imply
  LowerSemicontinuous I :=
-- proof
  lowerSemicontinuous_rate hμ hOn hOut


-- created on 2026-11-02
