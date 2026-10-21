import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset
open Nat


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  {α β : Type*}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (v1 v2 : α)
  (h : α → β)
  (hv1 : v1 ∈ S)
  (hv2 : v2 ∈ S) :
-- imply
  insert (h v1) (insert (h v2) (((S.erase v1).erase v2).image h)) = S.image h := by
-- proof
  ext b
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro (rfl | rfl | ⟨a, ⟨hne2, hne1, ha⟩, rfl⟩)
    · exact ⟨v1, hv1, rfl⟩
    · exact ⟨v2, hv2, rfl⟩
    · exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    by_cases heq1 : a = v1
    · left; rw [heq1]
    · by_cases heq2 : a = v2
      · right; left; rw [heq2]
      · right; right; exact ⟨a, ⟨heq2, heq1, ha⟩, rfl⟩


-- created on 2026-10-20
