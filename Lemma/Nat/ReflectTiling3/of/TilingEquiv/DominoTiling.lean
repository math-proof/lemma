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
  {n : ℕ}
-- given
  (T₁ T₂ : DominoTiling n 3)
  (h : DominoTiling.TilingEquiv T₁ T₂) :
-- imply
  DominoTiling.TilingEquiv (reflectTiling3 T₁) (reflectTiling3 T₂) := by
-- proof
  unfold DominoTiling.TilingEquiv at h ⊢
  have key : ∀ T : DominoTiling n 3,
      (reflectTiling3 T).dominos.image Domino.cells =
        (T.dominos.image Domino.cells).image (fun s => s.image reflectCell3) := by
    intro T
    ext S
    simp only [reflectTiling3, Finset.mem_image, Finset.mem_map, Finset.mem_attach, true_and,
      Subtype.exists, ← Function.Embedding.toFun_eq_coe]
    constructor
    ·
      rintro ⟨d, ⟨d0, hd0, rfl⟩, rfl⟩
      refine ⟨d0.cells, ⟨d0, hd0, rfl⟩, ?_⟩
      simp only [Domino.cells, reflectCell3, Finset.image_insert, Finset.image_singleton]
      rfl
    ·
      rintro ⟨s, ⟨d0, hd0, rfl⟩, rfl⟩
      refine ⟨_, ⟨d0, hd0, rfl⟩, ?_⟩
      simp only [Domino.cells, reflectCell3, Finset.image_insert, Finset.image_singleton]
      rfl
  rw [key T₁, key T₂, h]


-- created on 2026-10-20
