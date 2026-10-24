import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset
open Nat


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
  [DecidableEq α] [DecidableEq β]
-- given
  (S : Finset α)
  (v : α)
  (h : α → β)
  (hv : v ∈ S) :
-- imply
  insert (h v) ((S.erase v).image h) = S.image h := by
-- proof
  ext b
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase]
  constructor
  ·
    rintro (rfl | ⟨a, ⟨hne, ha⟩, rfl⟩)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, rfl⟩
  ·
    rintro ⟨a, ha, rfl⟩
    if heq : a = v then
      left
      rw [heq]
    else
      right
      exact ⟨a, ⟨heq, ha⟩, rfl⟩


-- created on 2026-10-20
