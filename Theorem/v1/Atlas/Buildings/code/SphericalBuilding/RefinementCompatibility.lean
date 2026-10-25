/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementCompatibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.RefinementFrame
import Lemma.Fin.SpacesVal.lt.SpacesAddVal1.of.IsStrictFlag
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.Fin
import Def.v1.Atlas.Buildings.code.SphericalBuilding.RefinementCompatibility


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The cardinality of `sigmaWitness i` is $i$. -/
theorem card_sigmaWitness_eq (i : Fin (n + 1)) :
    (sigmaWitness i).card = i.val := by
  simp only [sigmaWitness]
  rw [show Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ =
    Finset.univ.filter (fun j : Fin n => (j : ℕ) < i.val) from rfl]
  rw [Fin.card_filter_val_lt]
  exact Nat.min_eq_right (by omega)

/-- For a linearly independent family $\{v_i\}$ and a finite subset $S$, the dimension of
$\bigvee_{i \in S} k \cdot v_i$ equals $|S|$. -/
theorem finrank_biSup_span_singleton_eq_card {M : Type*}
    [AddCommGroup M] [Module k M]
    {ι : Type*} [Fintype ι] {v : ι → M}
    (hli : LinearIndependent k v) (S : Finset ι) :
    Module.finrank k ↥(⨆ i ∈ S, k ∙ v i) = S.card := by
  have heq : (⨆ i ∈ S, k ∙ v i) =
      Submodule.span k (Set.range (fun j : (S : Set ι) => v j)) := by
    conv_lhs => rw [show (⨆ i ∈ S, k ∙ v i) = ⨆ i : (S : Set ι), k ∙ v ↑i from by
      simp [iSup_subtype']]
    rw [← Submodule.span_range_eq_iSup]
  rw [heq]
  have hli' := hli.comp (fun j : (S : Set ι) => (j : ι)) Subtype.val_injective
  have : Set.range (fun j : (S : Set ι) => v ↑j) = Set.range (v ∘ fun j : (S : Set ι) => (j : ι)) := by
    ext; simp [Function.comp]
  rw [this, finrank_span_eq_card hli']
  simp [Fintype.card_coe]

/-- Equality criterion: $\bigvee_{i \in S} k \cdot v_i = W$ whenever the left side is contained
in $W$ and their dimensions agree. -/
theorem biSup_span_singleton_eq_of_le_of_finrank {M : Type*}
    [AddCommGroup M] [Module k M]
    {ι : Type*} [Fintype ι] {v : ι → M}
    (hli : LinearIndependent k v) (S : Finset ι)
    (W : Submodule k M) [FiniteDimensional k W]
    (hle : (⨆ i ∈ S, k ∙ v i) ≤ W)
    (hfr : Module.finrank k W = S.card) :
    (⨆ i ∈ S, k ∙ v i) = W := by
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_biSup_span_singleton_eq_card hli S, hfr]

end GLnBuilding
