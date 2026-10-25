import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnCommonApartmentUnconditional.Part3
open GLnBuilding


/--
[isChain_getElem_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma isChain_getElem_lt_eq
  [Field k]
  [Preorder α]
  {l : List α}
  {i j : ℕ}
-- given
  (hc : l.IsChain (· < ·))
  (hi : i < l.length)
  (hj : j < l.length)
  (hij : i < j) :
-- imply
  l[i] < l[j] := by
-- proof
  apply GLnBuilding.isChain_getElem_lt hc hi hj hij

/--
[chamberToCompleteFlag_isStrictFlag](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma chamberToCompleteFlag_isStrictFlag_eq
  [Field k]
  {n : ℕ}
  {σ : SubspaceFlag k n}
-- given
  (hchamber : IsChamber k n σ)
  (hn : n ≥ 2) :
-- imply
  (chamberToCompleteFlag σ hchamber hn).IsStrictFlag := by
-- proof
  apply GLnBuilding.chamberToCompleteFlag_isStrictFlag σ hchamber hn

/--
[chamberToCompleteFlag_contains](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma chamberToCompleteFlag_contains_eq
  [Field k]
  {n : ℕ}
  {σ : SubspaceFlag k n}
  {V : Submodule k (Vec k n)}
-- given
  (hchamber : IsChamber k n σ)
  (hn : n ≥ 2)
  (hV : V ∈ σ.chain) :
-- imply
  ∃ i : Fin (n + 1), (chamberToCompleteFlag σ hchamber hn).spaces i = V := by
-- proof
  apply GLnBuilding.chamberToCompleteFlag_contains σ hchamber hn V hV

/--
[schreierCell_increment_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma schreierCell_increment_symm_eq
  [Field k]
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
  {j : Fin (n + 1)}
-- given
  (_hσ : σ.IsStrictFlag)
  (_hτ : τ.IsStrictFlag)
  (hi : 0 < i.val)
  (hj : 0 < j.val) :
-- imply
  Module.finrank k ↥(schreierCell σ τ i hi j) - Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val - 1, by omega⟩) = Module.finrank k ↥(schreierCell τ σ j hj i) - Module.finrank k ↥(schreierCell τ σ j hj ⟨i.val - 1, by omega⟩) := by
-- proof
  apply GLnBuilding.schreierCell_increment_symm σ τ _hσ _hτ i hi j hj

/--
[jumpCol_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma jumpCol_transpose_eq
  [Field k]
  {σ τ : CompleteFlag k n}
  {i : Fin (n + 1)}
  {j : Fin n}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hi : 0 < i.val)
  (hj_spec : finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) = finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) + 1) :
-- imply
  finrank k ↥(schreierCell τ σ ⟨j.val + 1, by omega⟩ (by omega : 0 < j.val + 1) i) = finrank k ↥(schreierCell τ σ ⟨j.val + 1, by omega⟩ (by omega : 0 < j.val + 1) ⟨i.val - 1, by omega⟩) + 1 := by
-- proof
  apply GLnBuilding.jumpCol_transpose σ τ hσ hτ i hi j hj_spec

/--
[jumpCol_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma jumpCol_injective_eq
  [Field k]
  {σ τ : CompleteFlag k n}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag) :
-- imply
  Function.Injective (fun i : Fin n => jumpCol σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)) := by
-- proof
  apply GLnBuilding.jumpCol_injective σ τ hσ hτ

/--
[jhLine_mem_tau_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma jhLine_mem_tau_of_le_eq
  [Field k]
  {σ τ : CompleteFlag k n}
  {i : Fin n}
  {j : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag)
  (hij : (jumpCol σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)).val + 1 ≤ j.val) :
-- imply
  jhLine σ τ hσ hτ i ∈ τ.spaces j := by
-- proof
  apply GLnBuilding.jhLine_mem_tau_of_le σ τ hσ hτ i j hij

/--
[card_tauWitness_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma card_tauWitness_eq_eq
  [Field k]
  {σ τ : CompleteFlag k n}
  {j : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag) :
-- imply
  (tauWitness σ τ hσ hτ j).card = j.val := by
-- proof
  apply GLnBuilding.card_tauWitness_eq σ τ hσ hτ j

/--
[jordanHolderFrame_compatible_tau](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma jordanHolderFrame_compatible_tau_eq
  [Field k]
  {σ τ : CompleteFlag k n}
  [FiniteDimensional k (Vec k n)]
  {j : Fin (n + 1)}
-- given
  (hσ : σ.IsStrictFlag)
  (hτ : τ.IsStrictFlag) :
-- imply
  (jordanHolderFrame σ τ hσ hτ).IsCompatible k n (τ.spaces j) := by
-- proof
  apply GLnBuilding.jordanHolderFrame_compatible_tau σ τ hσ hτ j

/--
[no_proper_nonzero_subspace_of_le_one'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma no_proper_nonzero_subspace_of_le_one'_eq
  [Field k]
  {n : ℕ}
  {V : Submodule k (Vec k n)}
-- given
  (hn : n ≤ 1)
  (hbot : V ≠ ⊥)
  (htop : V ≠ ⊤) :
-- imply
  False := by
-- proof
  apply GLnBuilding.no_proper_nonzero_subspace_of_le_one' hn V hbot htop

/--
[subspaceFlag_empty_of_le_one'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean)
-/
@[path]
private lemma subspaceFlag_empty_of_le_one'_eq
  [Field k]
  {n : ℕ}
  {σ : SubspaceFlag k n}
-- given
  (hn : n ≤ 1) :
-- imply
  False := by
-- proof
  apply GLnBuilding.subspaceFlag_empty_of_le_one' hn σ


-- created on 2026-10-23
