import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem.Part2
open Equiv Fin SymGroupCoxeter


namespace SymGroupCoxeter

/--
[adjTransp_generates](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean)
-/
@[path]
lemma adjTransp_generates
  {n : ℕ} :
-- imply
  Submonoid.closure (Set.range (adjTransp n)) = ⊤ :=
-- proof
  Equiv.Perm.mclosure_swap_castSucc_succ n

end SymGroupCoxeter

namespace SymGroupCoxeter

/--
[toPermHom_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean)
-/
@[path]
lemma toPermHom_simple
  {n : ℕ}
  {i : Fin n} :
-- imply
  toPermHom n ((CoxeterMatrix.A n).simple i) = adjTransp n i :=
-- proof
  PresentedGroup.toGroup.of _

end SymGroupCoxeter

namespace SymGroupCoxeter

/--
[symGroup_coxeterSystem_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean)
-/
@[path]
lemma symGroup_coxeterSystem_simple
  {n : ℕ}
  {i : Fin n} :
-- imply
  (symGroup_coxeterSystem n).simple i = adjTransp n i := by
-- proof
  simp only [symGroup_coxeterSystem, CoxeterSystem.simple, symGroup_mulEquiv, adjTransp]
  exact typeA_symGroup_mulEquiv_apply n i

end SymGroupCoxeter

namespace SymGroupCoxeter

/--
[symGroup_isCoxeterGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean)
-/
@[path]
lemma symGroup_isCoxeterGroup
  {n : ℕ} :
-- imply
  IsCoxeterGroup (Equiv.Perm (Fin (n + 1))) :=
-- proof
  ⟨⟨Fin n, CoxeterMatrix.A n, ⟨symGroup_coxeterSystem n⟩⟩⟩

end SymGroupCoxeter

/--
[swap_mul_swap_cube_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean)
-/
@[path]
private lemma swap_mul_swap_cube_eq_one_eq
  [DecidableEq α]
  {a b c : α}
-- given
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c) :
-- imply
  (swap a b * swap b c) ^ 3 = 1 := by
-- proof
  apply SymGroupCoxeter.swap_mul_swap_cube_eq_one hab hbc hac

/--
[swap_mul_swap_cube_eq_one'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean)
-/
@[path]
private lemma swap_mul_swap_cube_eq_one'_eq
  [DecidableEq α]
  {a b c : α}
-- given
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hac : a ≠ c) :
-- imply
  (swap b c * swap a b) ^ 3 = 1 := by
-- proof
  apply SymGroupCoxeter.swap_mul_swap_cube_eq_one' hab hbc hac

/--
[adjTransp_isLiftable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean)
-/
@[path]
private lemma adjTransp_isLiftable_eq
  {n : ℕ} :
-- imply
  (CoxeterMatrix.A n).IsLiftable (adjTransp n) := by
-- proof
  apply SymGroupCoxeter.adjTransp_isLiftable n

/--
[adjTransp_relations_satisfied](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean)
-/
@[path]
private lemma adjTransp_relations_satisfied_eq
  {n : ℕ}
  {r : FreeGroup (Fin n)}
-- given
  (hr : r ∈ (CoxeterMatrix.A n).relationsSet) :
-- imply
  (FreeGroup.lift (adjTransp n)) r = 1 := by
-- proof
  apply SymGroupCoxeter.adjTransp_relations_satisfied n r hr


-- created on 2026-10-23
