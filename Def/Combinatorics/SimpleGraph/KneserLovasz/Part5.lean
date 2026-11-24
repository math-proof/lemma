module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Theorem.Combinatorics.SimpleGraph.KneserLovasz.Part3


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

def knPosMin {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) : Prop :=
  ∃ i, (true, i) ∈ knTop σ ∧ ∀ j ∈ (knTop σ).image Prod.snd, i ≤ j

open Classical in
noncomputable def knTightSet {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) :
    Finset (Finset (Finset (Bool × Fin n))) :=
  Finset.univ.filter (fun σ => knTight σ L ∧ ∅ ∉ σ)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
