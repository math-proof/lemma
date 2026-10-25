/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/KolmogorovMaximal.lean -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
open Finset BigOperators

/-!
# Kolmogorov maximal inequality

Finite product-space Kolmogorov maximal inequality: decompose the bad event by its
first hitting time, use centered future coordinates to kill the cross term, and identify
the second moment of the total sum with the sum of coordinate second moments.

Primary source: A. Kolmogoroff, "Über die Summen durch den Zufall bestimmter
unabhängiger Größen", Math. Ann. 99 (1928), 309–319, DOI 10.1007/BF01459098.
-/


namespace MathlibExt.Probability.KolmogorovMaximal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

variable {n : ℕ}

/-- Product weight of a joint outcome. -/
noncomputable def weight (p : Fin n → α → ℝ) (ω : Fin n → α) : ℝ :=
  ∏ i, p i (ω i)

/-- Partial sum up to `k` (inclusive). -/
noncomputable def partialSum (X : Fin n → α → ℝ) (k : Fin n)
    (ω : Fin n → α) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ k), X j (ω j)

/-- Total sum over all coordinates. -/
noncomputable def total (X : Fin n → α → ℝ) (ω : Fin n → α) : ℝ :=
  ∑ j, X j (ω j)

/-- First-hitting set: `|S_k| ≥ lam` and no earlier hit. -/
noncomputable def firstHit (X : Fin n → α → ℝ) (lam : ℝ) (k : Fin n) :
    Finset (Fin n → α) :=
  Finset.univ.filter
    (fun ω : Fin n → α =>
      |partialSum X k ω| ≥ lam ∧ ∀ j : Fin n, j < k → |partialSum X j ω| < lam)

/-- Bad event: some partial sum exceeds `lam`. Matches the wanted statement. -/
noncomputable def badSet (X : Fin n → α → ℝ) (lam : ℝ) : Finset (Fin n → α) :=
  Finset.univ.filter
    (fun ω : Fin n → α => ∃ i : Fin n, |partialSum X i ω| ≥ lam)

/-- Past/future splitting equivalence at `k`. -/
noncomputable def splitEquiv (k : Fin n) :
    (Fin n → α) ≃ ({j : Fin n // j ≤ k} → α) × ({j : Fin n // ¬ j ≤ k} → α) :=
  Equiv.piEquivPiSubtypeProd (fun j : Fin n => j ≤ k) (fun _ => α)

/-- Future sum after `k`. -/
noncomputable def remainder (X : Fin n → α → ℝ) (k : Fin n)
    (ω : Fin n → α) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j ≤ k), X j (ω j)

/-- Past-coordinate first-hitting set. -/
noncomputable def pastHit (X : Fin n → α → ℝ) (lam : ℝ) (k : Fin n) :
    Finset ({j : Fin n // j ≤ k} → α) := by
  classical
  exact Finset.univ.filter
    (fun u => ∃ v : {j : Fin n // ¬ j ≤ k} → α,
      (splitEquiv k).symm (u, v) ∈ firstHit X lam k)

end MathlibExt.Probability.KolmogorovMaximal
