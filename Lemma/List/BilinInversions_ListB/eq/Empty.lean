import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.InversionSet
open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

/--
[bilinInversions_nil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
lemma bilinInversions_nil
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  bilinInversions M ([] : List B) = ∅ := by
-- proof
  simp only [bilinInversions, Finset.filter_eq_empty_iff]
  intro s _
  simp only [wordSigma_nil, not_lt]
  have : e s s = 1 := by simp [e, Pi.single_apply]
  linarith

end CoxeterGroup

namespace CoxeterGroup

/--
[s_in_bilinInversions_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
lemma s_in_bilinInversions_singleton
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B} :
-- imply
  s ∈ bilinInversions M [s] := by
-- proof
  simp only [bilinInversions, Finset.mem_filter, Finset.mem_univ, true_and,
    wordSigma_singleton]
  rw [sigma_e_self]
  simp only [e, Pi.single_apply, if_pos rfl, neg_lt_zero]
  norm_num

end CoxeterGroup

namespace CoxeterGroup

/--
[sigma_e_other_t_component'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
lemma sigma_e_other_t_component'
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t) :
-- imply
  sigma M s (e t) t = 1 := by
-- proof
  simp only [sigma, bilinForm_e_e, e, Pi.single_apply]
  simp only [if_true, ite_not, Ne.symm hst, ite_false]
  ring

end CoxeterGroup

namespace CoxeterGroup

/--
[t_not_in_bilinInversions_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
lemma t_not_in_bilinInversions_singleton
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t) :
-- imply
  t ∉ bilinInversions M [s] := by
-- proof
  simp only [bilinInversions, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
    wordSigma_singleton]
  rw [sigma_e_other_t_component' M s t hst]
  norm_num

end CoxeterGroup

namespace CoxeterGroup

/--
[mem_bilinInversions_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean)
-/
@[path]
lemma mem_bilinInversions_iff
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {s : B} :
-- imply
  s ∈ bilinInversions M word ↔ wordSigma M word (e s) s < 0 := by
-- proof
  simp [bilinInversions]

end CoxeterGroup


-- created on 2026-10-23
