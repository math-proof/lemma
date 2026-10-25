import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
open CoxeterGroup


/--
[wordSigma_of_supported_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/PosOfAscentProof.lean)
-/
@[path]
private lemma wordSigma_of_supported_two_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {word : List B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
-- imply
  wordSigma M word v = fun u => v s * wordSigma M word (e s) u + v t * wordSigma M word (e t) u := by
-- proof
  apply CoxeterGroup.wordSigma_of_supported_two M s t hst word v hsupp

/--
[pos_of_ascent_case_b](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/PosOfAscentProof.lean)
-/
@[path]
private lemma pos_of_ascent_case_b_eq
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {n : ℕ}
  {init : List B}
  {s t : B}
-- given
  (ih : ∀ m < n, ∀ (word : List B) (s : B), word.length = m → cs.IsReduced word → cs.length (cs.wordProd word * cs.simple s) > cs.length (cs.wordProd word) → IsPositive (wordSigma M word (e s)))
  (hts : t ≠ s)
  (hred_init : cs.IsReduced init)
  (hasc_t : cs.length (cs.wordProd init * cs.simple t) > cs.length (cs.wordProd init))
  (hdesc_s : cs.length (cs.wordProd init * cs.simple s) < cs.length (cs.wordProd init))
  (hasc : cs.length (cs.wordProd (init ++ [t]) * cs.simple s) > cs.length (cs.wordProd (init ++ [t])))
  (hinit_len : init.length < n) :
-- imply
  IsPositive (wordSigma M (init ++ [t]) (e s)) := by
-- proof
  apply CoxeterGroup.pos_of_ascent_case_b M cs n ih init s t hts hred_init hasc_t hdesc_s hasc hinit_len

/--
[pos_of_ascent_proof](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/PosOfAscentProof.lean)
-/
@[path]
private lemma pos_of_ascent_proof_eq
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W} :
-- imply
  ∀ (n : ℕ) (word : List B) (s : B), word.length = n → cs.IsReduced word → cs.length (cs.wordProd word * cs.simple s) > cs.length (cs.wordProd word) → IsPositive (wordSigma M word (e s)) := by
-- proof
  apply CoxeterGroup.pos_of_ascent_proof M cs

/--
[pos_of_ascent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/PosOfAscentProof.lean)
-/
@[path]
private lemma pos_of_ascent_eq
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {s : B}
-- given
  (hred : cs.IsReduced word)
  (hasc : cs.length (cs.wordProd word * cs.simple s) > cs.length (cs.wordProd word)) :
-- imply
  IsPositive (wordSigma M word (e s)) := by
-- proof
  apply CoxeterGroup.pos_of_ascent M cs word s hred hasc

/--
[neg_of_descent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/PosOfAscentProof.lean)
-/
@[path]
private lemma neg_of_descent_eq
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {s : B}
-- given
  (hred : cs.IsReduced word)
  (hdesc : cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word)) :
-- imply
  IsNegative (wordSigma M word (e s)) := by
-- proof
  apply CoxeterGroup.neg_of_descent M cs word s hred hdesc


-- created on 2026-10-23
