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
import Theorem.Combinatorics.SimpleGraph.KneserLovasz.Part6
/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/


namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

def knPos {n : ℕ} (x : Finset (Bool × Fin n)) : Finset (Fin n) :=
  (x.filter (fun l => l.1 = true)).image Prod.snd

def knNegIdx {n : ℕ} (x : Finset (Bool × Fin n)) : Finset (Fin n) :=
  (x.filter (fun l => l.1 = false)).image Prod.snd

def knFp {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : ℕ :=
  (Finset.powersetCard k (knPos x)).sup (knCp C)

def knFm {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : ℕ :=
  (Finset.powersetCard k (knNegIdx x)).sup (knCp C)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
