import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnGapAnalysis.Part2
open GLnBuilding


/--
[insertIdx_eq_take_append_drop'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnGapAnalysis.lean)
-/
@[path]
private lemma insertIdx_eq_take_append_drop'_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {l : List α}
  {w : α}
  {i : ℕ}
-- given
  (hi : i ≤ l.length) :
-- imply
  l.insertIdx i w = l.take i ++ w :: l.drop i := by
-- proof
  apply GLnBuilding.insertIdx_eq_take_append_drop' k n hi

/--
[pairwise_insertIdx_of_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnGapAnalysis.lean)
-/
@[path]
private lemma pairwise_insertIdx_of_pairwise_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {R : α → α → Prop}
  {l : List α}
  {w : α}
  {i : ℕ}
-- given
  (hpw : l.Pairwise R)
  (hi : i ≤ l.length)
  (hbefore : ∀ x ∈ l.take i, R x w)
  (hafter : ∀ y ∈ l.drop i, R w y) :
-- imply
  (l.insertIdx i w).Pairwise R := by
-- proof
  apply GLnBuilding.pairwise_insertIdx_of_pairwise k n hpw hi hbefore hafter

/--
[isChain_insertIdx_of_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnGapAnalysis.lean)
-/
@[path]
private lemma isChain_insertIdx_of_isChain_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {R : α → α → Prop}
  [Trans R R R]
  {l : List α}
  {w : α}
  {i : ℕ}
-- given
  (hch : l.IsChain R)
  (hi : i ≤ l.length)
  (hbefore : ∀ x ∈ l.take i, R x w)
  (hafter : ∀ y ∈ l.drop i, R w y) :
-- imply
  (l.insertIdx i w).IsChain R := by
-- proof
  apply GLnBuilding.isChain_insertIdx_of_isChain k n hch hi hbefore hafter

/--
[insertIdx_ne_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnGapAnalysis.lean)
-/
@[path]
private lemma insertIdx_ne_of_ne_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {l : List α}
  {a b : α}
  {i : ℕ}
-- given
  (hne : a ≠ b)
  (hi : i ≤ l.length) :
-- imply
  l.insertIdx i a ≠ l.insertIdx i b := by
-- proof
  apply GLnBuilding.insertIdx_ne_of_ne k n hne hi


-- created on 2026-10-23
