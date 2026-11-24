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
public import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part19


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

lemma ntCode_rep5 (k : Fin 9) :
    ntCode (ntRep5 k) = ntRepCodes5.getD k.val [] :=
  ntCode_permOfCode _ _

lemma ntCode_rep6 (k : Fin 26) :
    ntCode (ntRep6 k) = ntRepCodes6.getD k.val [] :=
  ntCode_permOfCode _ _

lemma ntLabel_rep5 (k : Fin 9) :
    ntLabel5 (ntCode (ntRep5 k)) = k.val := by
  rw [ntCode_rep5]
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
-- Evaluating the `S₆` label table needs extra recursion depth.
lemma ntLabel_rep6 (k : Fin 26) :
    ntLabel6 (ntCode (ntRep6 k)) = k.val := by
  rw [ntCode_rep6]
  fin_cases k <;> decide

lemma ntRep5_pat (k : Fin 9) : ntPat 5 (ntRep5 k) := by
  apply ntHasPatB_sound
  rw [ntCode_rep5]
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
-- Evaluating the pattern test on the 26 `S₆` representatives needs extra recursion depth.
lemma ntRep6_pat (k : Fin 26) : ntPat 6 (ntRep6 k) := by
  apply ntHasPatB_sound
  rw [ntCode_rep6]
  fin_cases k <;> decide

end MetaMathlibExt
