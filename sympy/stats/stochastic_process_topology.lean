import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import sympy.stats.stochastic_process_types
import Lemma.Matrix.L1Norm.eq.One.of.StochasticVec
open Finset WithLp Matrix Filter Metric Bornology StochasticMatrix
open scoped Topology BigOperators Matrix

namespace StochasticMatrix

universe u
variable {S : Type u} [Fintype S]

instance (x : ↑(Simplex S)) : StochasticVec (WithLp.ofLp (x : l1Space S)) :=
  x.property

/-- Evaluation on coordinates is continuous in ℓ¹. -/
lemma continuous_coord (s : S) :
    Continuous fun f : l1Space S => WithLp.ofLp f s :=
  PiLp.continuous_apply (p := (1 : ENNReal)) (β := fun _ : S => ℝ) s

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

instance : CompleteSpace (↑(Simplex S) : Type _) :=
  IsClosed.completeSpace_coe (hs := inferInstance)

lemma simplex_subset_closedBall :
    (Simplex S) ⊆ closedBall (0 : l1Space S) 1 := by
  intro x hx
  have hx' : StochasticVec (WithLp.ofLp x) := hx
  have : ‖x‖ = ∑ s, |WithLp.ofLp x s| := (by simpa using (PiLp.norm_eq_sum (f := x)) : ‖x‖ = ∑ s, |WithLp.ofLp x s|)
  have hsum : ∑ s, |WithLp.ofLp x s| = ∑ s, WithLp.ofLp x s := by
    apply Finset.sum_congr rfl
    intro s _
    exact abs_of_nonneg (hx'.nonneg s)
  have : ‖x‖ = 1 := by
    rw [this, hsum, hx'.rowsum]
  simp [mem_closedBall_iff_norm, this]

instance : ProperSpace (l1Space S) := by
  infer_instance

lemma simples_is_compact : IsCompact (Simplex S) := by
  apply isCompact_of_isClosed_isBounded
  · infer_instance
  · exact (isBounded_iff_subset_closedBall (0 : l1Space S)).2 ⟨1, simplex_subset_closedBall⟩

end StochasticMatrix
