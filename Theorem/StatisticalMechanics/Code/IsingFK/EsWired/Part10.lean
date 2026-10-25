/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.IsingFK.EsWired.Part10
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


theorem card_constOnOpen_boundaryFixed {q : ℕ} (b : Fin q) (ω : ConfigSpace (Sym2 V))
    (v₀ : V) (hv₀ : bdry v₀) :
    Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ}
      = q ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1) := by
  classical
  have hcongr :
      Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ}
        = Nat.card {σ : V → Fin q // ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ} :=
    Nat.card_congr
      (Equiv.subtypeEquivRight fun σ => constOnOpen_boundaryFixed_iff G bdry b ω σ)
  rw [hcongr]
  set W := wiredSub G bdry ω with hW
  set c₀ := W.connectedComponentMk v₀ with hc₀
  
  have key : {σ : V → Fin q // ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ}
      ≃ {τ : W.ConnectedComponent → Fin q // τ c₀ = b} := by
    refine (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans ?_
    refine ((constOnWiredEquiv G bdry ω).subtypeEquiv ?_).symm
    intro τ
    show (τ c₀ = b ↔ BoundaryFixed bdry b ((constOnWiredEquiv G bdry ω) τ).1)
    constructor
    · intro h x hx
      show τ (W.connectedComponentMk x) = b
      rw [wiredSub_componentMk_eq_of_bdry G bdry hx hv₀]
      exact h
    · intro h
      have := h v₀ hv₀
      simpa [constOnWiredEquiv, hc₀] using this
  have hk : numClustersBC G (boundaryCliqueGraph bdry) ω = Fintype.card W.ConnectedComponent := by
    rw [numClustersBC]
    exact Nat.card_eq_fintype_card
  rw [Nat.card_congr key, Nat.card_congr (pinnedFunEquiv c₀ b),
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hk]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]


theorem esWeightWired_sum_spins {q : ℕ} (b : Fin q) (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    (∑ σ : V → Fin q, esWeightWired G bdry b p σ ω)
      = edgeProduct G p ω
        * (Finset.univ.filter
            (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ)).card := by
  classical
  have hpt : ∀ σ : V → Fin q, esWeightWired G bdry b p σ ω
      = if (ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ) then edgeProduct G p ω else 0 := by
    intro σ
    unfold esWeightWired
    rw [esWeight_eq_of_compatible]
    simp only [compatible_iff_constOnOpen]
    by_cases hb : BoundaryFixed bdry b σ <;> by_cases hc : ConstOnOpen G ω σ <;>
      simp [hb, hc]
  rw [Finset.sum_congr rfl (fun σ _ => hpt σ), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_comm]


theorem esWeightWired_sum_spins_eq_bcWeight {q : ℕ} (b : Fin q) (p : ℝ)
    (ω : ConfigSpace (Sym2 V)) (v₀ : V) (hv₀ : bdry v₀) (hq : 1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω) :
    (q : ℝ) * (∑ σ : V → Fin q, esWeightWired G bdry b p σ ω)
      = bcWeight G (boundaryCliqueGraph bdry) p (q : ℝ) ω := by
  classical
  rw [esWeightWired_sum_spins]
  have hcard :
      ((Finset.univ.filter
          (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ)).card : ℝ)
        = (q : ℝ) ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1) := by
    have hN : (Finset.univ.filter
          (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ)).card
        = q ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1) := by
      rw [← card_constOnOpen_boundaryFixed G bdry b ω v₀ hv₀,
        Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hN]; push_cast; rfl
  rw [hcard, bcWeight]
  
  set k := numClustersBC G (boundaryCliqueGraph bdry) ω with hk
  have hpow : (q : ℝ) * (q : ℝ) ^ (k - 1) = (q : ℝ) ^ k := by
    rw [← pow_succ']
    congr 1
    omega
  calc (q : ℝ) * (edgeProduct G p ω * (q : ℝ) ^ (k - 1))
      = edgeProduct G p ω * ((q : ℝ) * (q : ℝ) ^ (k - 1)) := by ring
    _ = edgeProduct G p ω * (q : ℝ) ^ k := by rw [hpow]


end IsingFK
end StatMech
