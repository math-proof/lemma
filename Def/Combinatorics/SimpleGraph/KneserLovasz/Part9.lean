module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Theorem.Combinatorics.SimpleGraph.KneserLovasz.Part7


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

def knMinIdx {n : ℕ} (x : Finset (Bool × Fin n))
    (hne : x.Nonempty) : Fin n :=
  (x.image Prod.snd).min' (hne.image _)

def knLabSmall {n : ℕ} (x : Finset (Bool × Fin n))
    (hne : x.Nonempty) (hn : 0 < n) : Bool × Fin n :=
  (decide ((true, knMinIdx x hne) ∈ x),
    ⟨min (x.card - 1) (n - 1), knMinLt _ hn⟩)

def knLabLargePos {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hk : 0 < k) (h2 : 2 * k ≤ n) (x : Finset (Bool × Fin n))
    (hfp : 1 ≤ knFp C x) : Bool × Fin n :=
  (true, ⟨(knFp C x - 1) + 2 * (k - 1),
    knLargeIdx_lt hk h2 _ hfp (knFp_le C x)⟩)

def knLabLargeNeg {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hk : 0 < k) (h2 : 2 * k ≤ n) (x : Finset (Bool × Fin n))
    (hfm : 1 ≤ knFm C x) : Bool × Fin n :=
  (false, ⟨(knFm C x - 1) + 2 * (k - 1),
    knLargeIdx_lt hk h2 _ hfm (knFm_le C x)⟩)

def knLab {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
    (x : Finset (Bool × Fin n)) : Bool × Fin n :=
  if _hx : x = ∅ then (true, ⟨n - 1, by omega⟩)
  else if _hsmall : knFp C x = 0 ∧ knFm C x = 0 then
    knLabSmall x (Finset.nonempty_iff_ne_empty.mpr _hx) hn
  else if hpos : knFm C x < knFp C x then
    knLabLargePos C hk h2 x (by omega)
  else
    knLabLargeNeg C hk h2 x (by
      have hfm0 : knFm C x ≠ 0 := by
        intro h0
        apply _hsmall
        refine ⟨?_, h0⟩
        omega
      exact Nat.pos_of_ne_zero hfm0)

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
