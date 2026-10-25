import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.SchreierRefinement
open GLnBuilding


/--
[schreierCell_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/SchreierRefinement.lean)
-/
@[path]
private lemma schreierCell_zero_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hi : 0 < i.val) :
-- imply
  schreierCell σ τ i hi ⟨0, Nat.zero_lt_succ n⟩ = σ.spaces ⟨i.val - 1, by omega⟩ := by
-- proof
  apply GLnBuilding.schreierCell_zero σ τ i hi

/--
[schreierCell_last](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/SchreierRefinement.lean)
-/
@[path]
private lemma schreierCell_last_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
-- given
  (hi : 0 < i.val) :
-- imply
  schreierCell σ τ i hi ⟨n, Nat.lt_succ_of_le le_rfl⟩ = σ.spaces i := by
-- proof
  apply GLnBuilding.schreierCell_last σ τ i hi

/--
[schreierCell_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/SchreierRefinement.lean)
-/
@[path]
private lemma schreierCell_mono_eq
  [Field k]
  {n : ℕ}
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
  {j j' : Fin (n + 1)}
-- given
  (hi : 0 < i.val)
  (hjj' : j ≤ j') :
-- imply
  schreierCell σ τ i hi j ≤ schreierCell σ τ i hi j' := by
-- proof
  apply GLnBuilding.schreierCell_mono σ τ i hi j j' hjj'


-- created on 2026-10-23
