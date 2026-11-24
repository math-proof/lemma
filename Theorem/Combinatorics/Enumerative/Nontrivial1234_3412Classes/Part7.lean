module
public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Relation
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic
public import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

/-- Value characterization of the two-block function. -/
lemma ntBetaFun_val {n j : ℕ} (hj : j + 1 ≤ n) (i : Fin n) :
    (ntBetaFun n j hj i).val =
      if i.val < j then j - 1 - i.val else n + j - 1 - i.val := by
  unfold ntBetaFun
  by_cases h : i.val < j
  · rw [dite_eq_left h, ite_eq_left h]
  · rw [dite_eq_right h, ite_eq_right h]

/-- The two-block function is an involution. -/
lemma ntBeta_invol {n j : ℕ} (hj : j + 1 ≤ n) (i : Fin n) :
    ntBetaFun n j hj (ntBetaFun n j hj i) = i := by
  have hi := i.is_lt
  apply Fin.ext_iff.mpr
  rw [ntBetaFun_val, ntBetaFun_val]
  by_cases h : i.val < j
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]
    omega

end MetaMathlibExt
