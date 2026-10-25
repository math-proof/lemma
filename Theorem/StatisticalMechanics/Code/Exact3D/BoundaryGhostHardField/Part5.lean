/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Def.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part5
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

theorem isingSpin_bToF_eq_spin {V : Type*} (τ : ConfigSpace V) (x : V) :
    FK.isingSpin (IsingFK.bToF (τ x)) = Ising.spin τ x := by
  simp [IsingFK.isingSpin_bToF, Ising.spin]


theorem isingBond_bToF_eq_bond {V : Type*} (τ : ConfigSpace V)
    (e : Sym2 V) :
    IsingFK.isingBond (fun x => IsingFK.bToF (τ x)) e =
      Ising.bond τ e := by
  induction e with
  | h x y =>
      rw [IsingFK.isingBond_mk, Ising.bond_mk]
      simp [isingSpin_bToF_eq_spin]


theorem boltzmannJ_one_flipV {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (τ : ConfigSpace V) :
    Sharpness.boltzmannJ G β (fun _ => 1)
        (Sharpness.FieldGhostDict.flipV τ) =
      Sharpness.boltzmannJ G β (fun _ => 1) τ := by
  classical
  unfold Sharpness.boltzmannJ
  congr 1
  refine congrArg (fun t : ℝ => β * t) ?_
  refine Finset.sum_congr rfl (fun e _he => ?_)
  rw [Sharpness.FieldGhostDict.bond_flipV]


theorem isingWiredWeight_bToF_eq_if
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V → Prop) [DecidablePred bdry]
    (β : ℝ) (τ : ConfigSpace V) :
    IsingFK.isingWiredWeight G bdry β
        (fun x => IsingFK.bToF (τ x)) =
      if (∀ x : V, bdry x → τ x = true) then
        Sharpness.boltzmannJ G β (fun _ => 1) τ
      else 0 := by
  classical
  by_cases h : ∀ x : V, bdry x → τ x = true
  · have hbf : IsingFK.BoundaryFixed bdry (0 : Fin 2)
        (fun x => IsingFK.bToF (τ x)) := by
      intro x hx
      change IsingFK.bToF (τ x) = 0
      rw [h x hx]
      rfl
    rw [if_pos h]
    unfold IsingFK.isingWiredWeight Sharpness.boltzmannJ
    rw [if_pos hbf]
    congr 1
    refine congrArg (fun t : ℝ => β * t) ?_
    refine Finset.sum_congr rfl (fun e _he => ?_)
    rw [isingBond_bToF_eq_bond]
    ring
  · have hbf : ¬ IsingFK.BoundaryFixed bdry (0 : Fin 2)
        (fun x => IsingFK.bToF (τ x)) := by
      intro hfixed
      apply h
      intro x hx
      have hx0 := hfixed x hx
      cases hτ : τ x <;> simp [IsingFK.bToF, hτ] at hx0 ⊢
    rw [if_neg h]
    unfold IsingFK.isingWiredWeight
    rw [if_neg hbf]


theorem isingWiredZ_eq_boolBoundaryBase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V → Prop) [DecidablePred bdry]
    (β : ℝ) :
    IsingFK.isingWiredZ G bdry β =
      ∑ τ : ConfigSpace V,
        if (∀ x : V, bdry x → τ x = true) then
          Sharpness.boltzmannJ G β (fun _ => 1) τ
        else 0 := by
  classical
  unfold IsingFK.isingWiredZ
  rw [← Equiv.sum_comp (boolConfigFin2Equiv V)
    (fun σ : V → Fin 2 => IsingFK.isingWiredWeight G bdry β σ)]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  change IsingFK.isingWiredWeight G bdry β
      (fun x => IsingFK.bToF (τ x)) = _
  exact isingWiredWeight_bToF_eq_if G bdry β τ


theorem isingWiredOnePointNumerator_eq_boolBoundaryBase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V → Prop) [DecidablePred bdry]
    (β : ℝ) (x : V) :
    (∑ σ : V → Fin 2,
        IsingFK.isingWiredWeight G bdry β σ * FK.isingSpin (σ x)) =
      ∑ τ : ConfigSpace V,
        if (∀ y : V, bdry y → τ y = true) then
          Sharpness.boltzmannJ G β (fun _ => 1) τ * Ising.spin τ x
        else 0 := by
  classical
  rw [← Equiv.sum_comp (boolConfigFin2Equiv V)
    (fun σ : V → Fin 2 =>
      IsingFK.isingWiredWeight G bdry β σ * FK.isingSpin (σ x))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  change IsingFK.isingWiredWeight G bdry β
      (fun x => IsingFK.bToF (τ x)) *
        FK.isingSpin (IsingFK.bToF (τ x)) = _
  rw [isingWiredWeight_bToF_eq_if G bdry β τ,
    isingSpin_bToF_eq_spin]
  by_cases h : ∀ y : V, bdry y → τ y = true <;> simp [h]


theorem boundaryGhostMismatchCount_split_eq_zero_iff (d n : ℕ)
    (b : Bool) (τ : ConfigSpace (FK.boxVerts d n)) :
    boundaryGhostMismatchCount d n
        (fun a => Option.rec b τ a : BoundaryGhostConfig d n) = 0 ↔
      ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = b := by
  simpa using boundaryGhostMismatchCount_eq_zero_iff d n
    (fun a => Option.rec b τ a : BoundaryGhostConfig d n)


theorem boundaryGhostAlignedLimitFactor_split_eq_if (d n : ℕ)
    (b : Bool) (τ : ConfigSpace (FK.boxVerts d n)) :
    boundaryGhostAlignedLimitFactor d n
        (fun a => Option.rec b τ a : BoundaryGhostConfig d n) =
      if (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = b) then
        1 else 0 := by
  unfold boundaryGhostAlignedLimitFactor countHardFieldLimitFactor
  by_cases h : ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = b
  · rw [if_pos h]
    have hz := (boundaryGhostMismatchCount_split_eq_zero_iff d n b τ).mpr h
    rw [if_pos hz]
  · rw [if_neg h]
    have hz : boundaryGhostMismatchCount d n
        (fun a => Option.rec b τ a : BoundaryGhostConfig d n) ≠ 0 := by
      intro hz
      exact h ((boundaryGhostMismatchCount_split_eq_zero_iff d n b τ).mp hz)
    rw [if_neg hz]


theorem boundaryGhostOnePointObservable_split_true (d n : ℕ)
    (τ : ConfigSpace (FK.boxVerts d n)) :
    boundaryGhostOnePointObservable d n
        (fun a => Option.rec true τ a : BoundaryGhostConfig d n) =
      Ising.spin τ (IsingFK.boxOrigin d n) := by
  rw [boundaryGhostOnePointObservable_eq]
  change Ising.spin τ (IsingFK.boxOrigin d n) * (1 : ℝ) =
    Ising.spin τ (IsingFK.boxOrigin d n)
  ring


theorem boundaryGhostOnePointObservable_split_false (d n : ℕ)
    (τ : ConfigSpace (FK.boxVerts d n)) :
    boundaryGhostOnePointObservable d n
        (fun a => Option.rec false τ a : BoundaryGhostConfig d n) =
      -(Ising.spin τ (IsingFK.boxOrigin d n)) := by
  rw [boundaryGhostOnePointObservable_eq]
  change Ising.spin τ (IsingFK.boxOrigin d n) * (-1 : ℝ) =
    -(Ising.spin τ (IsingFK.boxOrigin d n))
  ring


theorem boundaryGhostLimitDenominator_trueSector_eq_wiredZ
    (d n : ℕ) (β : ℝ) :
    (∑ τ : ConfigSpace (FK.boxVerts d n),
        boundaryGhostOriginalBase d n β
            (fun a => Option.rec true τ a : BoundaryGhostConfig d n) *
          boundaryGhostAlignedLimitFactor d n
            (fun a => Option.rec true τ a : BoundaryGhostConfig d n)) =
      IsingFK.isingWiredZ (FK.boxGraph d n) (FK.boxBoundary d n) β := by
  classical
  rw [isingWiredZ_eq_boolBoundaryBase]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [boundaryGhostAlignedLimitFactor_split_eq_if]
  by_cases h : ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = true
  · rw [if_pos h, if_pos h]
    change Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ * 1 =
      Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ
    ring
  · rw [if_neg h, if_neg h]
    ring


theorem boundaryGhostLimitDenominator_falseSector_eq_wiredZ
    (d n : ℕ) (β : ℝ) :
    (∑ τ : ConfigSpace (FK.boxVerts d n),
        boundaryGhostOriginalBase d n β
            (fun a => Option.rec false τ a : BoundaryGhostConfig d n) *
          boundaryGhostAlignedLimitFactor d n
            (fun a => Option.rec false τ a : BoundaryGhostConfig d n)) =
      IsingFK.isingWiredZ (FK.boxGraph d n) (FK.boxBoundary d n) β := by
  classical
  rw [isingWiredZ_eq_boolBoundaryBase]
  rw [← Equiv.sum_comp
    (Sharpness.FieldGhostDict.flipV_involutive
      (V := FK.boxVerts d n)).toPerm
    (fun τ : ConfigSpace (FK.boxVerts d n) =>
      if (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = true) then
        Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ else 0)]
  simp only [Function.Involutive.coe_toPerm]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [boundaryGhostAlignedLimitFactor_split_eq_if]
  have hiff :
      (∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true) ↔
      (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = false) := by
    constructor
    · intro h x hx
      have := h x hx
      unfold Sharpness.FieldGhostDict.flipV at this
      cases hτ : τ x <;> simp [hτ] at this ⊢
    · intro h x hx
      have := h x hx
      unfold Sharpness.FieldGhostDict.flipV
      rw [this]
      rfl
  by_cases hfalse :
      ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = false
  · have htrue : ∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true := hiff.mpr hfalse
    rw [if_pos hfalse, if_pos htrue]
    change Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ * 1 =
      Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1)
        (Sharpness.FieldGhostDict.flipV τ)
    rw [boltzmannJ_one_flipV]
    ring
  · have htrue : ¬ ∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true := by
      intro ht
      exact hfalse (hiff.mp ht)
    rw [if_neg hfalse, if_neg htrue]
    ring


theorem boundaryGhostLimitDenominator_eq_two_mul_wiredZ
    (d n : ℕ) (β : ℝ) :
    finiteFactorLimitDenominator
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostAlignedLimitFactor d n) =
      2 * IsingFK.isingWiredZ
        (FK.boxGraph d n) (FK.boxBoundary d n) β := by
  classical
  unfold finiteFactorLimitDenominator
  rw [Sharpness.FieldGhostDict.sum_option_config, Fintype.sum_bool,
    boundaryGhostLimitDenominator_trueSector_eq_wiredZ,
    boundaryGhostLimitDenominator_falseSector_eq_wiredZ]
  ring


theorem boundaryGhostLimitNumerator_trueSector_eq_wiredNumerator
    (d n : ℕ) (β : ℝ) :
    (∑ τ : ConfigSpace (FK.boxVerts d n),
        boundaryGhostOriginalBase d n β
            (fun a => Option.rec true τ a : BoundaryGhostConfig d n) *
          boundaryGhostAlignedLimitFactor d n
            (fun a => Option.rec true τ a : BoundaryGhostConfig d n) *
          boundaryGhostOnePointObservable d n
            (fun a => Option.rec true τ a : BoundaryGhostConfig d n)) =
      ∑ σ : FK.boxVerts d n → Fin 2,
        IsingFK.isingWiredWeight (FK.boxGraph d n) (FK.boxBoundary d n) β σ *
          FK.isingSpin (σ (IsingFK.boxOrigin d n)) := by
  classical
  rw [isingWiredOnePointNumerator_eq_boolBoundaryBase]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [boundaryGhostAlignedLimitFactor_split_eq_if,
    boundaryGhostOnePointObservable_split_true]
  by_cases h : ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = true
  · rw [if_pos h, if_pos h]
    change Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ * 1 *
        Ising.spin τ (IsingFK.boxOrigin d n) =
      Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ *
        Ising.spin τ (IsingFK.boxOrigin d n)
    ring
  · rw [if_neg h, if_neg h]
    ring


theorem boundaryGhostLimitNumerator_falseSector_eq_wiredNumerator
    (d n : ℕ) (β : ℝ) :
    (∑ τ : ConfigSpace (FK.boxVerts d n),
        boundaryGhostOriginalBase d n β
            (fun a => Option.rec false τ a : BoundaryGhostConfig d n) *
          boundaryGhostAlignedLimitFactor d n
            (fun a => Option.rec false τ a : BoundaryGhostConfig d n) *
          boundaryGhostOnePointObservable d n
            (fun a => Option.rec false τ a : BoundaryGhostConfig d n)) =
      ∑ σ : FK.boxVerts d n → Fin 2,
        IsingFK.isingWiredWeight (FK.boxGraph d n) (FK.boxBoundary d n) β σ *
          FK.isingSpin (σ (IsingFK.boxOrigin d n)) := by
  classical
  rw [isingWiredOnePointNumerator_eq_boolBoundaryBase]
  rw [← Equiv.sum_comp
    (Sharpness.FieldGhostDict.flipV_involutive
      (V := FK.boxVerts d n)).toPerm
    (fun τ : ConfigSpace (FK.boxVerts d n) =>
      if (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = true) then
        Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ *
          Ising.spin τ (IsingFK.boxOrigin d n)
      else 0)]
  simp only [Function.Involutive.coe_toPerm]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [boundaryGhostAlignedLimitFactor_split_eq_if,
    boundaryGhostOnePointObservable_split_false]
  have hiff :
      (∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true) ↔
      (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = false) := by
    constructor
    · intro h x hx
      have := h x hx
      unfold Sharpness.FieldGhostDict.flipV at this
      cases hτ : τ x <;> simp [hτ] at this ⊢
    · intro h x hx
      have := h x hx
      unfold Sharpness.FieldGhostDict.flipV
      rw [this]
      rfl
  by_cases hfalse :
      ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = false
  · have htrue : ∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true := hiff.mpr hfalse
    rw [if_pos hfalse, if_pos htrue]
    change Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1) τ * 1 *
        (-(Ising.spin τ (IsingFK.boxOrigin d n))) =
      Sharpness.boltzmannJ (FK.boxGraph d n) β (fun _ => 1)
          (Sharpness.FieldGhostDict.flipV τ) *
        Ising.spin (Sharpness.FieldGhostDict.flipV τ) (IsingFK.boxOrigin d n)
    rw [boltzmannJ_one_flipV, Sharpness.FieldGhostDict.spin_flipV]
    ring
  · have htrue : ¬ ∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        Sharpness.FieldGhostDict.flipV τ x = true := by
      intro ht
      exact hfalse (hiff.mp ht)
    rw [if_neg hfalse, if_neg htrue]
    ring


theorem boundaryGhostLimitNumerator_eq_two_mul_wiredNumerator
    (d n : ℕ) (β : ℝ) :
    finiteFactorLimitNumerator
        (Finset.univ : Finset (BoundaryGhostConfig d n))
        (boundaryGhostOriginalBase d n β)
        (boundaryGhostOnePointObservable d n)
        (boundaryGhostAlignedLimitFactor d n) =
      2 * (∑ σ : FK.boxVerts d n → Fin 2,
        IsingFK.isingWiredWeight (FK.boxGraph d n) (FK.boxBoundary d n) β σ *
          FK.isingSpin (σ (IsingFK.boxOrigin d n))) := by
  classical
  unfold finiteFactorLimitNumerator
  rw [Sharpness.FieldGhostDict.sum_option_config, Fintype.sum_bool,
    boundaryGhostLimitNumerator_trueSector_eq_wiredNumerator,
    boundaryGhostLimitNumerator_falseSector_eq_wiredNumerator]
  ring


theorem boundaryGhostAlignedLimitRatio_eq_wiredOnePoint
    (d n : ℕ) (β : ℝ) :
    finiteFactorLimitRatio
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      (boundaryGhostOriginalBase d n β)
      (boundaryGhostOnePointObservable d n)
      (boundaryGhostAlignedLimitFactor d n) =
        IsingFK.isingWiredOnePoint
          (FK.boxGraph d n) (FK.boxBoundary d n) β
          (IsingFK.boxOrigin d n) := by
  unfold finiteFactorLimitRatio IsingFK.isingWiredOnePoint
  rw [boundaryGhostLimitNumerator_eq_two_mul_wiredNumerator,
    boundaryGhostLimitDenominator_eq_two_mul_wiredZ]
  exact mul_div_mul_left _ _ two_ne_zero


theorem boundaryGhostOriginalBase_pos (d n : ℕ) (β : ℝ)
    (σ : BoundaryGhostConfig d n) :
    0 < boundaryGhostOriginalBase d n β σ := by
  unfold boundaryGhostOriginalBase
  exact Sharpness.boltzmannJ_pos (FK.boxGraph d n) β (fun _ => 1)
    (fun x => σ (some x))


theorem boundaryGhostAlignedLimitDenominator_ne_zero
    (d n : ℕ) (β : ℝ) :
    finiteFactorLimitDenominator
      (Finset.univ : Finset (BoundaryGhostConfig d n))
      (boundaryGhostOriginalBase d n β)
      (boundaryGhostAlignedLimitFactor d n) ≠ 0 := by
  classical
  unfold boundaryGhostAlignedLimitFactor
  refine countHardFieldLimitDenominator_ne_zero_of_exists_pos
    (s := (Finset.univ : Finset (BoundaryGhostConfig d n)))
    (penalty := boundaryGhostMismatchCount d n)
    (base := boundaryGhostOriginalBase d n β) ?_ ?_
  · intro σ _hσ _hzero
    exact (boundaryGhostOriginalBase_pos d n β σ).le
  · let σ0 : BoundaryGhostConfig d n := fun _ => true
    refine ⟨σ0, Finset.mem_univ σ0, ?_, ?_⟩
    · rw [boundaryGhostMismatchCount_eq_zero_iff]
      intro x _hx
      rfl
    · exact boundaryGhostOriginalBase_pos d n β σ0


end Exact3D
end StatMech
