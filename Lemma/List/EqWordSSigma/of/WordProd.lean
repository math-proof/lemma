import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
open Finset BigOperators CoxeterGroup


/--
[wordSigma_eq_of_wordProd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/WordSigmaInvariance.lean)
-/
@[path]
private lemma wordSigma_eq_of_wordProd_eq_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  [Group W]
  {cs : CoxeterSystem M W}
  {word1 word2 : List B}
  {v : B → ℝ}
-- given
  (h : cs.wordProd word1 = cs.wordProd word2) :
-- imply
  wordSigma M word1 v = wordSigma M word2 v := by
-- proof
  apply CoxeterGroup.wordSigma_eq_of_wordProd_eq M cs word1 word2 h v


-- created on 2026-10-23
