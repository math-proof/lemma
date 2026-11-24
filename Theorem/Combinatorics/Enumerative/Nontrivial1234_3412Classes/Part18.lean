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
public import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part18


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

set_option maxRecDepth 100000 in

lemma ntRepCode5_mem (k : Fin 9) :
    ntRepCodes5.getD k.val [] ∈ List.permutations' (List.range 5) := by
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
-- Deciding membership among the 720 codes of `S₆` needs extra recursion depth.
lemma ntRepCode6_mem (k : Fin 26) :
    ntRepCodes6.getD k.val [] ∈ List.permutations' (List.range 6) := by
  fin_cases k <;> decide

end MetaMathlibExt
