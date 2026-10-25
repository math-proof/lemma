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
import Abbrev.Combinatorics.SimpleGraph.KneserLovasz
/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/


namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj x y := Disjoint x.val y.val ∧ x ≠ y
  symm.symm := by
    intro a b ⟨hdisj, hne⟩
    exact ⟨hdisj.symm, hne.symm⟩
  loopless.irrefl := by
    intro a ⟨_, hne⟩
    exact hne rfl

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
