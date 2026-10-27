import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (T : DominoTiling n m)
  (c : Cell)
  (d₁ d₂ : Domino)
  (hd₁ : d₁ ∈ T.dominos)
  (hd₂ : d₂ ∈ T.dominos)
  (hc₁ : c ∈ d₁.cells)
  (hc₂ : c ∈ d₂.cells) :
-- imply
  d₁ = d₂ := by
-- proof
  by_contra hne
  have hdisj := T.pairwise_disjoint d₁ hd₁ d₂ hd₂ hne
  rw [Finset.disjoint_iff_ne] at hdisj
  exact hdisj c hc₁ c hc₂ rfl


-- created on 2026-10-20
