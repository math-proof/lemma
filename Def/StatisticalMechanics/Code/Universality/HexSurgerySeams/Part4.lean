/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part4


namespace StatMech.Universality

open Complex HexWalk List Filter

open scoped Topology BigOperators


noncomputable def hexHWDataClosed (c : ℕ → ℝ) (υ : ℕ → ℝ) (x : ℝ) (N : ℕ)
    (hυnn : ∀ T, 0 ≤ υ T)
    (hmul : Multipliable (fun T => 1 + υ T))
    (Dn : Type) [Fintype Dn]
    (wtγ : Dn → ℝ) (wtγ_nn : ∀ d, 0 ≤ wtγ d)
    (partial_eq : ∑ d, wtγ d = ∑ n ∈ Finset.range N, c n * x ^ n)
    (decomp : Dn → Finset ℕ × Finset ℕ)
    (decomp_inj : Function.Injective decomp)
    (weight_bound : ∀ d, wtγ d ≤ (x ^ 2)⁻¹ *
      ((∏ T ∈ (decomp d).1, υ T) * (∏ T ∈ (decomp d).2, υ T))) :
    HexHWDataRecon c υ x N where
  S := Finset ℕ
  Dn := Dn
  Dn_fintype := inferInstance
  wtγ := wtγ
  wtS := fun s => ∏ T ∈ s, υ T
  wtγ_nn := wtγ_nn
  wtS_nn := fun _ => Finset.prod_nonneg (fun T _ => hυnn T)
  S_summable := hexSeams_summable_finset_prod υ hυnn hmul
  partial_eq := partial_eq
  half_sum_eq := tsum_finset_prod_eq_tprod υ hυnn hmul
  decomp := decomp
  decomp_inj := decomp_inj
  weight_bound := weight_bound


end StatMech.Universality
