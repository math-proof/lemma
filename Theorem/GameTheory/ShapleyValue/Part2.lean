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
import Def.GameTheory.ShapleyValue.Part2
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

/-- Every game is a combination of unanimity games with Möbius coefficients. -/
theorem game_expansion (v : CoopGame Player) :
    v = ∑ T ∈ Finset.univ.powerset.filter (fun T => T ≠ ∅),
      mobiusCoeff v T • unanimity T := by
  classical
  ext S
  have hF : ∀ T ∈ Finset.univ.powerset.filter (fun T => T ≠ ∅),
      (mobiusCoeff v T • unanimity T).charFun S
      = (if (T : Set Player) ⊆ S then mobiusCoeff v T else 0) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    rw [charFun_smul, unanimity_charFun hT.2]
    by_cases h : (T : Set Player) ⊆ S <;> simp [h]
  rw [charFun_sum, Finset.sum_congr rfl hF, ← Finset.sum_filter]
  have hsub_iff : ∀ T : Finset Player, T ⊆ S.toFinset ↔ (T : Set Player) ⊆ S := by
    intro T
    have hcoe : ((S.toFinset : Finset Player) : Set Player) = S := Set.coe_toFinset S
    have h := Finset.coe_subset (s₁ := T) (s₂ := S.toFinset)
    rw [hcoe] at h
    exact h.symm
  have hset : (Finset.univ.powerset.filter (fun T => T ≠ ∅)).filter
        (fun T : Finset Player => (T : Set Player) ⊆ S)
      = S.toFinset.powerset.filter (fun T => T ≠ ∅) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨-, hne⟩, hsub⟩
      exact ⟨(hsub_iff T).mpr hsub, hne⟩
    · rintro ⟨hsub, hne⟩
      exact ⟨⟨Finset.subset_univ T, hne⟩, (hsub_iff T).mp hsub⟩
  rw [hset]
  have hinv := mobius_inversion v S.toFinset
  rw [Set.coe_toFinset] at hinv
  rw [hinv]
  have hsub0 : S.toFinset.powerset.filter (fun T => T ≠ ∅) ⊆ S.toFinset.powerset :=
    Finset.filter_subset _ _
  have hzero : ∀ T ∈ S.toFinset.powerset,
      T ∉ S.toFinset.powerset.filter (fun T => T ≠ ∅) → mobiusCoeff v T = 0 := by
    intro T hT hnT
    have hTeq : T = ∅ := by
      by_contra hne
      rw [Finset.mem_filter] at hnT
      exact hnT ⟨hT, hne⟩
    subst hTeq
    exact mobiusCoeff_empty v
  exact (Finset.sum_subset hsub0 hzero).symm

omit [DecidableEq Player] in
theorem shapley_uniqueness (φ₁ φ₂ : CoopGame Player →ₗ[ℝ] (Player → ℝ))
    (h1e : IsEfficient φ₁) (h1s : IsSymmetric φ₁)
    (h1n : SatisfiesNullPlayerAxiom φ₁)
    (h2e : IsEfficient φ₂) (h2s : IsSymmetric φ₂)
    (h2n : SatisfiesNullPlayerAxiom φ₂) :
    φ₁ = φ₂ := by
  apply LinearMap.ext
  intro v
  rw [game_expansion v, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [map_smul, map_smul]
  have hagree := agree_on_unanimity φ₁ φ₂ h1e h1s h1n h2e h2s h2n T
  rw [hagree]

omit [DecidableEq Player] [Fintype Player] in
theorem mobiusCoeff_add (v w : CoopGame Player) (T : Finset Player) :
    mobiusCoeff (v + w) T = mobiusCoeff v T + mobiusCoeff w T := by
  unfold mobiusCoeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R _
  rw [charFun_add, mul_add]

omit [DecidableEq Player] [Fintype Player] in
theorem mobiusCoeff_smul (c : ℝ) (v : CoopGame Player) (T : Finset Player) :
    mobiusCoeff (c • v) T = c * mobiusCoeff v T := by
  unfold mobiusCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  rw [charFun_smul]
  ring

end MathlibExt.GameTheory.ShapleyValue
