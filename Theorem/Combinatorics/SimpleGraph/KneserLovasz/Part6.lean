/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Def.Combinatorics.SimpleGraph.KneserLovasz.Part7
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
