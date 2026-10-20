import Mathlib
import sympy.Basic
import sympy.atlas.InformationTheory.HammingBall
open scoped BigOperators
open Hamming


/--
[mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean)
-/
@[path]
private lemma mem_ball_eq
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {x y : ι → F}
  {e : ℕ} :
-- imply
  y ∈ ball x e ↔ hammingDist x y ≤ e := by
-- proof
  apply Hamming.mem_ball

/--
[card_ball](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean)
-/
@[path]
private lemma card_ball_eq
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {x : ι → F}
  {e : ℕ} :
-- imply
  (ball x e).card =
    ∑ k ∈ Finset.range (e + 1),
    (Fintype.card ι).choose k * (Fintype.card F - 1) ^ k := by
-- proof
  apply Hamming.card_ball x e

/--
[card_ball_fin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingBall.lean)
-/
@[path]
private lemma card_ball_fin_eq
  [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
  {n q : ℕ}
  {x : Fin n → F}
  {e : ℕ}
-- given
  (hn : 0 < n)
  (hq : Fintype.card F = q)
  (_hq₂ : 2 ≤ q) :
-- imply
  (ball x e).card = ∑ k ∈ Finset.range (e + 1), n.choose k * (q - 1) ^ k := by
-- proof
  apply Hamming.card_ball_fin hn hq _hq₂ x e


-- created on 2026-10-20
