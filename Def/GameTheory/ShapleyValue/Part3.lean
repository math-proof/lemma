/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ext
import Theorem.GameTheory.ShapleyValue.Part2
/-! # Shapley value characterization for cooperative games

Existence and uniqueness of the linear value satisfying efficiency, symmetry,
and the null-player axiom, via unanimity games and Möbius inversion on the
Boolean lattice.

Source: L. S. Shapley, "A Value for n-Person Games," Contributions to the
Theory of Games II, Annals of Mathematics Studies 28, Princeton University
Press (1953), 307--317; modern DOI `10.1515/9781400881970-018`.

Source-fidelity note: Shapley's printed argument (pp. 308--312) works with
superadditive games on a player universe with finite carriers, with axioms of
full permutation equivariance, efficiency for every carrier, and aggregation.
What is proved here is an adapted fixed-finite-player vector-space
characterization: it quantifies over arbitrary normalized set functions on one
fixed finite player type, packages aggregation together with real homogeneity
as linearity, and uses invariant-game symmetry (equal payoffs when a
permutation fixes the game), grand-coalition efficiency, and a null-player
axiom. This characterization is mathematically coherent as stated, but it is
this adapted formulation rather than a literal transcription of the source
theorem.
-/


namespace MathlibExt.GameTheory.ShapleyValue

variable {Player : Type*} [DecidableEq Player] [Fintype Player]

attribute [local instance] Classical.propDecidable

noncomputable def shapleyLM : CoopGame Player →ₗ[ℝ] (Player → ℝ) where
  toFun v := fun i =>
    ∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
      mobiusCoeff v T / (T.card : ℝ)
  map_add' v w := by
    funext i
    change (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff (v + w) T / (T.card : ℝ))
        = (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff v T / (T.card : ℝ))
        + (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff w T / (T.card : ℝ))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    rw [mobiusCoeff_add, add_div]
  map_smul' c v := by
    funext i
    change (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff (c • v) T / (T.card : ℝ))
        = c • (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff v T / (T.card : ℝ))
    rw [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [mobiusCoeff_smul, mul_div_assoc]

end MathlibExt.GameTheory.ShapleyValue
