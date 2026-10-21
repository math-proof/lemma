import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings.reflectTiling3_dominos_minCol_maxCol
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
  {n : ℕ}
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree) :
-- imply
  (reflectTiling3 T).isFaultfree := by
-- proof
  intro k hk_ge1 hk_lt_n hfault
  refine hfree k hk_ge1 hk_lt_n ?_
  ·
    refine ⟨hfault.1, hfault.2.1, ?_⟩
    ·
      intro d hd
      obtain ⟨d', hd'_mem, hd'_min, hd'_max⟩ :=
        _root_.Nat.DominoTilings.reflectTiling3_dominos_minCol_maxCol T d hd
      have hd'_no_span := hfault.2.2 d' hd'_mem
      rwa [← hd'_min, ← hd'_max]


-- created on 2026-10-20
