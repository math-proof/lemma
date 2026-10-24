/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean -/

import Mathlib.Data.Fintype.Perm
import sympy.atlas.Combinatorics.Enumerative.RStirlingFirstAlternatingExpansion
import Lemma.Finset.Enumerative.RStirlingFirstAlternatingExpansion
import Lemma.Finset.Enumerative.MeshPatternStirlingRecursion
import sympy.atlas.Combinatorics.Enumerative.MeshPatternStirlingRecursion
import Lemma.Finset.Enumerative.MeshPatternGeneratingFunction
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

section
namespace MetaMathlibExt

private def meshWantedMatch (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  (∀ h : Fin n, h < i → σ h < σ i) ∧
    k - 1 ≤ (Finset.univ.filter fun q : Fin n =>
      i < q ∧ (∀ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) → q < m) ∧ σ i < σ q).card

private instance decMeshWantedMatch (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    DecidablePred (meshWantedMatch k σ) := fun i => by
  unfold meshWantedMatch
  infer_instance

private def meshWantedZero (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) ∧ k ≤ m.val + 1

private instance decMeshWantedZero (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Decidable (meshWantedZero k σ) := by
  unfold meshWantedZero
  infer_instance

private def meshWantedCount (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (meshWantedMatch k σ)).card +
    (if meshWantedZero k σ then 1 else 0)
end MetaMathlibExt
end
