import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.RootSystem
open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

/--
[sigma_maps_roots](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/RootSystem.lean)
-/
@[path]
private lemma sigma_maps_roots
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {α : B → ℝ}
-- given
  (hα : isRoot M α) :
-- imply
  isRoot M (sigma M s α) := by
-- proof
  obtain ⟨word, t, rfl⟩ := hα
  exact ⟨s :: word, t, rfl⟩

end CoxeterGroup

namespace CoxeterGroup

/--
[neg_e_isNegative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/RootSystem.lean)
-/
@[path]
private lemma neg_e_isNegative
  [DecidableEq B]
  [Fintype B]
  {s : B} :
-- imply
  isNegativeVec (fun t => -(e s t)) :=
-- proof
  ⟨s, by simp [e]⟩

end CoxeterGroup

namespace CoxeterGroup

/--
[sigma_e_other_t_component](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/RootSystem.lean)
-/
@[path]
private lemma sigma_e_other_t_component
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t) :
-- imply
  sigma M s (e t) t = 1 := by
-- proof
  simp only [sigma, bilinForm_e_e]
  simp only [e, Pi.single_apply, ite_true, ite_eq_right (Ne.symm hst)]
  ring

end CoxeterGroup

namespace CoxeterGroup

/--
[wordSigma_reverse_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/RootSystem.lean)
-/
@[path]
private lemma wordSigma_reverse_cancel
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {v : B → ℝ} :
-- imply
  wordSigma M word (wordSigma M word.reverse v) = v := by
-- proof
  induction word generalizing v with
  | nil => simp
  | cons s rest ih =>
    simp only [wordSigma_cons, List.reverse_cons, wordSigma_append, wordSigma_nil]
    rw [ih]
    exact sigma_involution M s v

end CoxeterGroup


-- created on 2026-10-23
-- updated on 2026-10-24
