import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.SemidirectExistence
open GeometricAlgebra


/--
[isCompl_of_isOppositeFlag](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/SemidirectExistence.lean)
-/
@[path]
private lemma isCompl_of_isOppositeFlag_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F F' : Flag k V}
  {i : Fin F.len}
-- given
  (hopp : Flag.isOppositeFlag F F') :
-- imply
  IsCompl (F.spaces i) (F'.spaces ⟨F'.len - 1 - i.val, by have := hopp.1; omega⟩) := by
-- proof
  apply GeometricAlgebra.isCompl_of_isOppositeFlag F F' hopp i

/--
[opposite_top_is_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/SemidirectExistence.lean)
-/
@[path]
private lemma opposite_top_is_bot_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F F' : Flag k V}
-- given
  (hopp : Flag.isOppositeFlag F F')
  (hlen : 0 < F.len)
  (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤) :
-- imply
  F'.spaces ⟨0, by have := by
-- proof
  apply GeometricAlgebra.opposite_top_is_bot F F' hopp hlen hcov

/--
[semidirect_existence_len_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/SemidirectExistence.lean)
-/
@[path]
private lemma semidirect_existence_len_one_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F F' : Flag k V}
  {p : V ≃ₗ[k] V}
-- given
  (hopp : Flag.isOppositeFlag F F')
  (hlen1 : F.len = 1)
  (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
  (hp : ∀ i : Fin F.len, (F.spaces i).map p.toLinearMap = F.spaces i) :
-- imply
  ∃ (d u : V ≃ₗ[k] V), (∀ i : Fin F.len, (F.spaces i).map d.toLinearMap = F.spaces i) ∧ (∀ i : Fin F'.len, (F'.spaces i).map d.toLinearMap = F'.spaces i) ∧ (∀ i : Fin F.len, (F.spaces i).map u.toLinearMap = F.spaces i) ∧ (∀ i : Fin F.len, ∀ v ∈ F.spaces i, u.toLinearMap v - v ∈ if _ : (i : ℕ) = 0 then (⊥ : Submodule k V) else F.spaces ⟨i.val - 1, by omega⟩) ∧ p.toLinearMap = d.toLinearMap.comp u.toLinearMap := by
-- proof
  apply GeometricAlgebra.semidirect_existence_len_one F F' hopp hlen1 hcov p hp

/--
[map_eq_of_forall_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/SemidirectExistence.lean)
-/
@[path]
private lemma map_eq_of_forall_mem_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W : Submodule k V}
  {e : V ≃ₗ[k] V}
-- given
  (h0 : ∀ w ∈ W, e w ∈ W)
  (h1 : ∀ w ∈ W, e.symm w ∈ W) :
-- imply
  W.map e.toLinearMap = W := by
-- proof
  apply GeometricAlgebra.map_eq_of_forall_mem W e h0 h1

/--
[block_diagonal_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/SemidirectExistence.lean)
-/
@[path]
private lemma block_diagonal_decomp_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {W W' : Submodule k V}
  {p : V ≃ₗ[k] V}
-- given
  (hc : IsCompl W W')
  (hpW : W.map p.toLinearMap = W) :
-- imply
  ∃ (d₀ u₀ : V ≃ₗ[k] V), (W.map d₀.toLinearMap = W) ∧ (W'.map d₀.toLinearMap = W') ∧ (W.map u₀.toLinearMap = W) ∧ (∀ v : V, u₀.toLinearMap v - v ∈ W) ∧ p.toLinearMap = d₀.toLinearMap.comp u₀.toLinearMap ∧ (∀ w ∈ W, d₀ w = p w) := by
-- proof
  apply GeometricAlgebra.block_diagonal_decomp W W' hc p hpW

/--
[preserves_of_unipotent_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/SemidirectExistence.lean)
-/
@[path]
private lemma preserves_of_unipotent_le_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {S W : Submodule k V}
  {e : V ≃ₗ[k] V}
-- given
  (hunip : ∀ v : V, e.toLinearMap v - v ∈ W)
  (hle : W ≤ S) :
-- imply
  S.map e.toLinearMap = S := by
-- proof
  apply GeometricAlgebra.preserves_of_unipotent_le S W e hunip hle

/--
[semidirect_existence_inductive_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/SemidirectExistence.lean)
-/
@[path]
private lemma semidirect_existence_inductive_step_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {F F' : Flag k V}
  {p : V ≃ₗ[k] V}
-- given
  (hopp : Flag.isOppositeFlag F F')
  (hlen : 2 ≤ F.len)
  (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
  (hp : ∀ i : Fin F.len, (F.spaces i).map p.toLinearMap = F.spaces i)
  (ih : ∀ (G G' : Flag k V), G.len = G'.len → (∀ (hlen_eq : G.len = G'.len) (i : Fin G.len), G.spaces i ⊔ G'.spaces ⟨G'.len - 1 - i.val, by omega⟩ = ⊤ ∧ G.spaces i ⊓ G'.spaces ⟨G'.len - 1 - i.val, by omega⟩ = ⊥) → G.len < F.len → (hGpos : 0 < G.len) → G.spaces ⟨G.len - 1, by omega⟩ = ⊤ → ∀ (q : V ≃ₗ[k] V), (∀ j : Fin G.len, (G.spaces j).map q.toLinearMap = G.spaces j) → ∃ (d u : V ≃ₗ[k] V), (∀ j : Fin G.len, (G.spaces j).map d.toLinearMap = G.spaces j) ∧ (∀ j : Fin G'.len, (G'.spaces j).map d.toLinearMap = G'.spaces j) ∧ (∀ j : Fin G.len, (G.spaces j).map u.toLinearMap = G.spaces j) ∧ (∀ j : Fin G.len, ∀ v ∈ G.spaces j, u.toLinearMap v - v ∈ if _ : (j : ℕ) = 0 then (⊥ : Submodule k V) else G.spaces ⟨j.val - 1, by omega⟩) ∧ q.toLinearMap = d.toLinearMap.comp u.toLinearMap) :
-- imply
  ∃ (d u : V ≃ₗ[k] V), (∀ i : Fin F.len, (F.spaces i).map d.toLinearMap = F.spaces i) ∧ (∀ i : Fin F'.len, (F'.spaces i).map d.toLinearMap = F'.spaces i) ∧ (∀ i : Fin F.len, (F.spaces i).map u.toLinearMap = F.spaces i) ∧ (∀ i : Fin F.len, ∀ v ∈ F.spaces i, u.toLinearMap v - v ∈ if _ : (i : ℕ) = 0 then (⊥ : Submodule k V) else F.spaces ⟨i.val - 1, by omega⟩) ∧ p.toLinearMap = d.toLinearMap.comp u.toLinearMap := by
-- proof
  apply GeometricAlgebra.semidirect_existence_inductive_step F F' hopp hlen hcov p hp ih


-- created on 2026-10-23
