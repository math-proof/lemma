import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance
open GeometricAlgebra


/--
[submodule_map_of_finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagEquivalenceInstance.lean)
-/
@[path]
private lemma submodule_map_of_finrank_eq_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [AddCommGroup M]
  [Module k M]
  [FiniteDimensional k M]
  {W₁ W₂ : Submodule k M}
-- given
  (hdim : Module.finrank k W₁ = Module.finrank k W₂) :
-- imply
  ∃ e : M ≃ₗ[k] M, W₁.map e.toLinearMap = W₂ := by
-- proof
  apply GeometricAlgebra.submodule_map_of_finrank_eq W₁ W₂ hdim

/--
[adjustment_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagEquivalenceInstance.lean)
-/
@[path]
private lemma adjustment_equiv_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {W U₁ U₂ : Submodule k V}
-- given
  (hle₁ : W ≤ U₁)
  (hle₂ : W ≤ U₂)
  (hdim : Module.finrank k U₁ = Module.finrank k U₂) :
-- imply
  ∃ e : V ≃ₗ[k] V, (∀ w ∈ W, e w = w) ∧ U₁.map e.toLinearMap = U₂ := by
-- proof
  apply GeometricAlgebra.adjustment_equiv W U₁ U₂ hle₁ hle₂ hdim

/--
[map_eq_of_pointwise_fix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagEquivalenceInstance.lean)
-/
@[path]
private lemma map_eq_of_pointwise_fix_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {S W : Submodule k V}
  {e : V ≃ₗ[k] V}
-- given
  (hfix : ∀ w ∈ W, e w = w)
  (hle : S ≤ W) :
-- imply
  S.map e.toLinearMap = S := by
-- proof
  apply GeometricAlgebra.map_eq_of_pointwise_fix S W e hfix hle

/--
[map_trans_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagEquivalenceInstance.lean)
-/
@[path]
private lemma map_trans_eq_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {S : Submodule k V}
  {e₁ e₂ : V ≃ₗ[k] V} :
-- imply
  S.map (e₁.trans e₂).toLinearMap = (S.map e₁.toLinearMap).map e₂.toLinearMap := by
-- proof
  apply GeometricAlgebra.map_trans_eq S e₁ e₂

/--
[flag_equiv_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagEquivalenceInstance.lean)
-/
@[path]
private lemma flag_equiv_aux_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V] :
-- imply
  ∀ (n : ℕ) (spaces₁ spaces₂ : Fin n → Submodule k V) (_ : StrictMono spaces₁) (_ : StrictMono spaces₂) (_ : ∀ i : Fin n, Module.finrank k (spaces₁ i) = Module.finrank k (spaces₂ i)), ∃ e : V ≃ₗ[k] V, ∀ i : Fin n, (spaces₁ i).map e.toLinearMap = spaces₂ i := by
-- proof
  apply GeometricAlgebra.flag_equiv_aux

/--
[flag_equiv_of_sameType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagEquivalenceInstance.lean)
-/
@[path]
private lemma flag_equiv_of_sameType_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V] :
-- imply
  ∀ F₁ F₂ : Flag k V, F₁.sameType F₂ → ∃ (e : V ≃ₗ[k] V) (hlen : F₁.len = F₂.len), ∀ i : Fin F₁.len, (F₁.spaces i).map e.toLinearMap = F₂.spaces (i.cast hlen) := by
-- proof
  apply GeometricAlgebra.flag_equiv_of_sameType k V


-- created on 2026-10-23
