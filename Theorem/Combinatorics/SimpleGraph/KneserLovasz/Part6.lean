module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Def.Combinatorics.SimpleGraph.KneserLovasz.Part7


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

theorem knCp_eq {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    {A : Finset (Fin n)} (h : A.card = k) :
    knCp C A = (C ⟨A, h⟩).val + 1 :=
  dite_eq_left h

theorem knCp_ne {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    {A : Finset (Fin n)} (h : A.card ≠ k) : knCp C A = 0 :=
  dite_eq_right h

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
