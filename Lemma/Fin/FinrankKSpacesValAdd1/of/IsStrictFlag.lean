import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps
open GLnBuilding


/--
[CompleteFlag.IsStrictFlag.finrank_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementDimJumps.lean)
-/
@[path]
private lemma main
  [Field k]
  {n : ℕ}
  {σ : CompleteFlag k n}
  {j : Fin n}
-- given
  (hσ : σ.IsStrictFlag) :
-- imply
  Module.finrank k ↥(σ.spaces ⟨j.val + 1, by omega⟩) = Module.finrank k ↥(σ.spaces ⟨j.val, by omega⟩) + 1 := by
-- proof
  rw [hσ ⟨j.val + 1, by omega⟩, hσ ⟨j.val, by omega⟩]


/--
[schreierCell_eq_sup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementDimJumps.lean)
-/
private lemma schreierCell_eq_sup_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
  {j : Fin (n + 1)}
-- given
  (hi : 0 < i.val) :
-- imply
  schreierCell σ τ i hi j = σ.spaces ⟨i.val - 1, by omega⟩ ⊔ (σ.spaces i ⊓ τ.spaces j) := by
-- proof
  apply GLnBuilding.schreierCell_eq_sup σ τ i hi j

/--
[schreierCell_finrank_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementDimJumps.lean)
-/
private lemma schreierCell_finrank_step_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
  {j : Fin n}
-- given
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) ≤ Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) + 1 := by
-- proof
  apply GLnBuilding.schreierCell_finrank_step σ τ hτ i hi j

/--
[schreierCell_row_total](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementDimJumps.lean)
-/
private lemma schreierCell_row_total_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hi : 0 < i.val) :
-- imply
  Module.finrank k ↥(schreierCell σ τ i hi ⟨n, Nat.lt_succ_of_le le_rfl⟩) = Module.finrank k ↥(schreierCell σ τ i hi ⟨0, Nat.zero_lt_succ n⟩) + 1 := by
-- proof
  apply GLnBuilding.schreierCell_row_total σ τ hσ i hi


-- created on 2026-10-23
-- updated on 2026-10-24
