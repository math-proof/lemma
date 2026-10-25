import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.SimpleReflectionInversions
open Finset BigOperators CoxeterGroup


namespace Definitions
end Definitions
namespace CoxeterGroup

/--
[sigma_e_other_t_component'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
private lemma sigma_e_other_t_component'
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t) :
-- imply
  sigma M s (e t) t = 1 := by
-- proof
  simp only [sigma, e, Pi.single_apply]
  simp only [ite_true, Ne.symm hst, ite_false]
  ring

end CoxeterGroup

namespace CoxeterGroup

/--
[s_in_bilinInversions_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
private lemma s_in_bilinInversions_singleton
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B} :
-- imply
  s ∈ bilinInversions M [s] := by
-- proof
  simp only [bilinInversions, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [wordSigma_singleton, sigma_e_self]
  simp only [e, Pi.single_apply, neg_lt_zero]
  norm_num

end CoxeterGroup

namespace CoxeterGroup

/--
[t_not_in_bilinInversions_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
private lemma t_not_in_bilinInversions_singleton
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t) :
-- imply
  t ∉ bilinInversions M [s] := by
-- proof
  simp only [bilinInversions, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rw [wordSigma_singleton, sigma_e_other_t_component' hst]
  norm_num

end CoxeterGroup

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
    exact t_not_in_bilinInversions_singleton (Ne.symm hne) ht
  ·
    intro ht
    subst ht
    exact s_in_bilinInversions_singleton

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
