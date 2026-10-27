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
  (T : DominoTiling n 3) :
-- imply
  ∀ d ∈ T.dominos, ∃ d' ∈ (reflectTiling3 T).dominos, d'.minCol = d.minCol ∧ d'.maxCol = d.maxCol := by
-- proof
  intro d hd
  simp only [reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      ← Function.Embedding.toFun_eq_coe]
  refine ⟨_, ⟨d, hd, rfl⟩, ?_⟩
  ·
    simp only [Domino.minCol, Domino.maxCol]
    constructor <;> rfl


-- created on 2026-10-20
