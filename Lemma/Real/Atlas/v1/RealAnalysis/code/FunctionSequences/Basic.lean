import Mathlib
import sympy.Basic
import Def.v1.Atlas.RealAnalysis.code.FunctionSequences.Basic
open Filter Topology


/--
[uniform_convergence_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/Basic.lean)
-/
@[path]
lemma uniform_convergence_iff
  {f : ℕ → ℝ → ℝ}
  {g : ℝ → ℝ}
  {S : Set ℝ} :
-- imply
  TendstoUniformlyOn f g atTop S ↔ ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, ∀ x ∈ S, := by
-- proof
  rw [Metric.tendstoUniformlyOn_iff]
  constructor
  · intro h ε hε
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (h ε hε)
    exact ⟨M, fun n hn x hx => by rw [← Real.dist_eq, dist_comm]; exact hM n hn x hx⟩
  · intro h ε hε
    obtain ⟨M, hM⟩ := h ε hε
    rw [Filter.eventually_atTop]
    exact ⟨M, fun n hn x hx => by rw [Real.dist_eq, ← abs_sub_comm]; exact hM n hn x hx⟩

/--
[weierstrass_m_test](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/Basic.lean)
-/
@[path]
lemma weierstrass_m_test
  {f : ℕ → ℝ → ℝ}
  {M : ℕ → ℝ}
  {S : Set ℝ}
-- given
  (hM : ∀ j, ∀ x ∈ S, |f j x| ≤ M j)
  (hMsum : Summable M) :
-- imply
  (∀ x ∈ S, Summable (fun j => f j x)) ∧ TendstoUniformlyOn (fun n x => ∑ j ∈ Finset.range n, f j x) (fun x => ∑' j, f j x) Filter.atTop S := by
-- proof
  have hfu : ∀ n, ∀ x ∈ S, ‖f n x‖ ≤ M n := by
    intro n x hx
    rw [Real.norm_eq_abs]
    exact hM n x hx
  exact ⟨fun x hx => Summable.of_norm_bounded (g := M) hMsum (fun i => hfu i x hx),
    tendstoUniformlyOn_tsum_nat hMsum hfu⟩


-- created on 2026-10-23
