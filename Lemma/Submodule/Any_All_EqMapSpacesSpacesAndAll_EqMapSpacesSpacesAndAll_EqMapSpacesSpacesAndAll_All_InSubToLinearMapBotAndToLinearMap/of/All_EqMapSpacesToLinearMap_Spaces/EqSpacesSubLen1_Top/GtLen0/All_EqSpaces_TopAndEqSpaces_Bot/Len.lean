import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.SemidirectExistenceInstance
open GeometricAlgebra


/--
[semidirect_existence_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/SemidirectExistenceInstance.lean)
-/
@[path]
private lemma semidirect_existence_compl_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {G G' : Flag k V}
  {q : V ≃ₗ[k] V}
-- given
  (hlen_eq : G.len = G'.len)
  (hcompl : ∀ (h : G.len = G'.len) (i : Fin G.len), G.spaces i ⊔ G'.spaces ⟨G'.len - 1 - i.val, by omega⟩ = ⊤ ∧ G.spaces i ⊓ G'.spaces ⟨G'.len - 1 - i.val, by omega⟩ = ⊥)
  (hlen_pos : 0 < G.len)
  (hcov : G.spaces ⟨G.len - 1, by omega⟩ = ⊤)
  (hq : ∀ j : Fin G.len, (G.spaces j).map q.toLinearMap = G.spaces j) :
-- imply
  ∃ (d u : V ≃ₗ[k] V), (∀ j : Fin G.len, (G.spaces j).map d.toLinearMap = G.spaces j) ∧ (∀ j : Fin G'.len, (G'.spaces j).map d.toLinearMap = G'.spaces j) ∧ (∀ j : Fin G.len, (G.spaces j).map u.toLinearMap = G.spaces j) ∧ (∀ j : Fin G.len, ∀ v ∈ G.spaces j, u.toLinearMap v - v ∈ if h : (j : ℕ) = 0 then (⊥ : Submodule k V) else G.spaces ⟨j.val - 1, by omega⟩) ∧ q.toLinearMap = d.toLinearMap.comp u.toLinearMap := by
-- proof
  apply GeometricAlgebra.semidirect_existence_compl G G' hlen_eq hcompl hlen_pos hcov q hq


-- created on 2026-10-23
