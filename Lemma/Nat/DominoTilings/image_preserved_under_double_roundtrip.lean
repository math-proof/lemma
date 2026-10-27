import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
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
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
-- given
  (S : Finset α)
  (f : (x : α) → x ∈ S → β)
  (g : β → α)
  (h : α → γ)
  (hfgh : ∀ x (hx : x ∈ S), h (g (f x hx)) = h x) :
-- imply
  ((S.attach.image (fun ⟨x, hx⟩ => f x hx)).image g).image h = S.image h := by
-- proof
  ext c
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
  constructor
  ·
    rintro ⟨b, ⟨a, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, hx, (hfgh x hx).symm⟩
  ·
    rintro ⟨x, hx, rfl⟩
    exact ⟨g (f x hx), ⟨f x hx, ⟨x, hx, rfl⟩, rfl⟩, hfgh x hx⟩


-- created on 2026-10-20
