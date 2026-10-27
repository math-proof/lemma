import Instance.Probability.Process.StochasticProcessTypes.Part3
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Lemma.Matrix.L1Norm.eq.One.of.StochasticVec
import Mathlib.Topology.Instances.Matrix
import Theorem.Probability.Process.StochasticProcess
open Finset WithLp Matrix Filter Metric Bornology Topology Function PiLp
open scoped Topology BigOperators Matrix NNReal
set_option maxHeartbeats 800000

universe u
variable {S : Type u} [Fintype S]

/-!
# Stochastic processes

Topology of the probability simplex, the Markov operator on it, and related
instances — aligned with
[sympy.stats.stochastic_process](https://github.com/sympy/sympy/blob/master/sympy/stats/stochastic_process.py).

Core typeclasses live in `Instance.Probability.Process.StochasticProcessTypes.Part3`.
-/


instance : IsClosed (Simplex S) := by
  let E := l1Space S
  have h1 : IsClosed {f : E | ∀ s, 0 ≤ WithLp.ofLp f s} := by
    have hcl (s : S) : IsClosed {f : E | 0 ≤ WithLp.ofLp f s} := by
      have hev := continuous_coord (S := S) s
      have half : IsClosed {x : ℝ | 0 ≤ x} := isClosed_le continuous_const continuous_id
      simpa [Set.preimage] using half.preimage hev
    simpa [Set.ofPred_forall] using isClosed_iInter hcl
  have h2 : IsClosed {f : E | (∑ s, WithLp.ofLp f s) = 1} := by
    have hsum : Continuous fun f : E => ∑ s, WithLp.ofLp f s :=
      continuous_finsetSum (s := (Finset.univ : Finset S))
        fun s _ => continuous_coord (S := S) s
    have htarget : IsClosed ({x : ℝ | x = 1} : Set ℝ) := by simp
    simpa [Set.preimage] using htarget.preimage hsum
  have hinter := IsClosed.inter h1 h2
  convert hinter using 1
  ext f
  constructor
  · intro hf
    exact ⟨hf.nonneg, hf.rowsum⟩
  · intro ⟨hnonneg, hsum⟩
    exact ⟨hnonneg, hsum⟩

instance : CompleteSpace (Simplex S : Type _) :=
  IsClosed.completeSpace_coe (hs := inferInstance)

instance : ProperSpace (l1Space S) := by
  infer_instance

