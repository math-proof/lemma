import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.SphericalBuilding.BasisFromFlagProof
open GLnBuilding


/--
[strictMono_nat_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/BasisFromFlagProof.lean)
-/
@[path]
private lemma strictMono_nat_id_eq
  [Field k]
  {n : ℕ}
  {n : ℕ}
  {g : Fin (n + 1) → ℕ}
-- given
  (hg : StrictMono g)
  (_h0 : g ⟨0, Nat.zero_lt_succ n⟩ = 0)
  (hn : g ⟨n, Nat.lt_succ_of_le le_rfl⟩ = n) :
-- imply
  ∀ j : Fin (n + 1), g j = j.val := by
-- proof
  apply GLnBuilding.strictMono_nat_id g hg _h0 hn

/--
[linearIndependent_of_not_mem_span_predecessors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/BasisFromFlagProof.lean)
-/
@[path]
private lemma linearIndependent_of_not_mem_span_predecessors_eq
  [Field k]
  {n : ℕ}
  [AddCommGroup V]
  [Module k V]
  {m : ℕ}
  {v : Fin m → V}
-- given
  (h : ∀ j : Fin m, v j ∉ Submodule.span k (v '' {i : Fin m | i.val < j.val})) :
-- imply
  LinearIndependent k v := by
-- proof
  apply GLnBuilding.linearIndependent_of_not_mem_span_predecessors v h


-- created on 2026-10-23
