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
  {n : ℕ}
-- given
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree) :
-- imply
  (reflectTiling3 T).isFaultfree := by
-- proof
  intro k hk_ge1 hk_lt_n hfault -- Then T also has a fault at k
  apply hfree k hk_ge1 hk_lt_n
  ·
    constructor
    · exact hfault.1
    constructor
    · exact hfault.2.1
    ·
      intro d hd -- Get the corresponding reflected domino
      obtain ⟨d', hd'_mem, hd'_min, hd'_max⟩ := reflectTiling3_dominos_minCol_maxCol T d hd -- d' doesn't span column k (since there's a fault)
      have hd'_no_span := hfault.2.2 d' hd'_mem -- But d has the same minCol and maxCol as d'
      rwa [← hd'_min, ← hd'_max]


-- created on 2026-10-20
