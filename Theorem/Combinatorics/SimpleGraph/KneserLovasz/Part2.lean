module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Def.Combinatorics.SimpleGraph.KneserLovasz.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/
namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

theorem knGAdj_symm {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n)
    (σ τ : Finset (Finset (Bool × Fin n))) (h : knGAdj L σ τ) : knGAdj L τ σ := by
  classical
  obtain ⟨hs, ht, hdoor⟩ := h
  exact ⟨ht, hs, hdoor.elim Or.inr Or.inl⟩

theorem knGAdj_irrefl {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n)
    (σ : Finset (Finset (Bool × Fin n))) (h : knGAdj L σ σ) : False := by
  classical
  obtain ⟨_, _, hdoor⟩ := h
  rcases hdoor with ⟨v, hv, heq, _⟩ | ⟨w, hw, heq, _⟩
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hv] at hcc
    omega
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hw] at hcc
    omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
