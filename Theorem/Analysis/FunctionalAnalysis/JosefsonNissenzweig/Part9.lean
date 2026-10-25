/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Theorem.Analysis.FunctionalAnalysis.BanachLimit.Part5
import Lemma.Filter.Any_And_Eq_1AndAll_EqAndAll_Eq
import Lemma.Set.Any_All_Any_All_LtNormSubOrHasUniformL1LowerBound.of.IsBounded_Range
import Theorem.Analysis.FunctionalAnalysis.RosenthalL1.Part13
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part10


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_wholeGroupIndex_strictMono {p : ℕ} (hp : 0 < p)
    {u : ℕ → ℕ} (hu : StrictMono u) :
    StrictMono (jnWholeGroupIndex p u) := by
  intro m n hmn
  have hdiv : m / p ≤ n / p := Nat.div_le_div_right hmn.le
  rcases hdiv.eq_or_lt with hdiv | hdiv
  · have hm : p * (m / p) + m % p = m := by
      simpa [Nat.mul_comm] using Nat.div_add_mod m p
    have hn : p * (n / p) + n % p = n := by
      simpa [Nat.mul_comm] using Nat.div_add_mod n p
    have hmod : m % p < n % p := by
      rw [hdiv] at hm
      omega
    unfold jnWholeGroupIndex
    rw [hdiv]
    exact Nat.add_lt_add_left hmod _
  · have hu' : u (m / p) < u (n / p) := hu hdiv
    have hmmod : m % p < p := Nat.mod_lt m hp
    unfold jnWholeGroupIndex
    have hleft : p * u (m / p) + m % p < p * (u (m / p) + 1) := by
      rw [Nat.mul_succ]
      omega
    have hmiddle : p * (u (m / p) + 1) ≤ p * u (n / p) :=
      Nat.mul_le_mul_left p hu'
    omega

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
