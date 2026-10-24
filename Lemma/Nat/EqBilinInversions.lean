import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.SimpleReflectionInversions
open Finset BigOperators CoxeterGroup


namespace Definitions
end Definitions
namespace CoxeterGroup

/--
[bilinInversions_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SimpleReflectionInversions.lean)
-/
@[path]
private lemma bilinInversions_singleton
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B} :
-- imply
  bilinInversions M [s] = {s} := by
-- proof
  ext t
  simp only [Finset.mem_singleton]
  constructor
  ·
    intro ht
    by_contra hne
    exact t_not_in_bilinInversions_singleton M s t (Ne.symm hne) ht
  ·
    intro ht
    rw [ht]
    exact s_in_bilinInversions_singleton M s

end CoxeterGroup

/--
[wordSigma_append_s_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SimpleReflectionInversions.lean)
-/
@[path]
private lemma wordSigma_append_s_neg_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {s : B} :
-- imply
  wordSigma M (word ++ [s]) (e s) = fun t => -(wordSigma M word (e s) t) := by
-- proof
  apply CoxeterGroup.wordSigma_append_s_neg M word s


-- created on 2026-10-24
