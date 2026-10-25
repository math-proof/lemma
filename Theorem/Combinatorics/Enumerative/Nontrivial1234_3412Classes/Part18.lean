/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part18


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
