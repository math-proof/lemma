import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
  {α β : Type*}
  [DecidableEq α]
  [DecidableEq β]
-- given
  (S : Finset α)
  (v w : α)
  (f : α → β)
  (hv : v ∈ S)
  (hf : f v = f w) :
-- imply
  (insert w (S.erase v)).image f = S.image f := by
-- proof
  ext b
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨a, (rfl | ⟨hne, ha⟩), hab⟩
    · refine ⟨v, hv, ?_⟩; rw [hf]; exact hab
    · exact ⟨a, ha, hab⟩
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a = v
    · subst h; exact ⟨w, Or.inl rfl, hf.symm⟩
    · exact ⟨a, Or.inr ⟨h, ha⟩, rfl⟩


-- created on 2026-10-20
