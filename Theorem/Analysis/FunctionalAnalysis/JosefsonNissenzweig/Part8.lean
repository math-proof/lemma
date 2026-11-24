module
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.RCLike.Extend
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Theorem.Analysis.FunctionalAnalysis.BanachLimit.Part5
public import Theorem.Filter.Any_And_Eq_1AndAll_EqAndAll_Eq
public import Theorem.Set.Any_All_Any_All_LtNormSubOrHasUniformL1LowerBound.of.IsBounded_Range
public import Theorem.Analysis.FunctionalAnalysis.RosenthalL1.Part13
public import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_exists_strictMono_of_cofinal (P : ℕ → Prop)
    (hP : ∀ N, ∃ n, N ≤ n ∧ P n) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ ∀ n, P (u n) := by
  classical
  let u : ℕ → ℕ := Nat.rec (Classical.choose (hP 0))
    (fun _ previous => Classical.choose (hP (previous + 1)))
  have huP : ∀ n, P (u n) := by
    intro n
    cases n with
    | zero => exact (Classical.choose_spec (hP 0)).2
    | succ n => exact (Classical.choose_spec (hP (u n + 1))).2
  have hstep : ∀ n, u n < u (n + 1) := by
    intro n
    exact Nat.lt_of_succ_le (Classical.choose_spec (hP (u n + 1))).1
  exact ⟨u, strictMono_nat_of_lt_succ hstep, huP⟩

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
