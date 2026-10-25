import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc14reimerinduct
open Finset StatMech StatMech.Walls


/--
[rc14_mem_boxE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc14reimerinduct.lean)
-/
@[path]
private lemma rc14_mem_boxE_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc14_boxE E 𝒜 ℬ ↔ S ⊆ E ∧ ∃ K L : Finset α, Disjoint K L ∧ K ⊆ S ∧ L ⊆ S ∧ K ∈ 𝒜 ∧ L ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc14_mem_boxE E 𝒜 ℬ S

/--
[rc14_mem_reflE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc14reimerinduct.lean)
-/
@[path]
private lemma rc14_mem_reflE_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc14_reflE E 𝒜 ℬ ↔ S ⊆ E ∧ S ∈ 𝒜 ∧ E \ S ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc14_mem_reflE E 𝒜 ℬ S


-- created on 2026-10-23
