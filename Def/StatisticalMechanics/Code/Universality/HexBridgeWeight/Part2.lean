/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeWeight.lean -/

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
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part2


namespace StatMech.Universality

open List

open scoped BigOperators


noncomputable def hexHWDataReconOfDomination (c : ℕ → ℝ) (υ : ℕ → ℝ) (x : ℝ) (N : ℕ)
    (hx : 0 < x)
    (hυnn : ∀ T, 0 ≤ υ T)
    (hmul : Multipliable (fun T => 1 + υ T))
    (Dn : Type) [Fintype Dn]
    (wtγ : Dn → ℝ) (wtγ_nn : ∀ d, 0 ≤ wtγ d)
    (partial_eq : ∑ d, wtγ d = ∑ n ∈ Finset.range N, c n * x ^ n)
    (wt : ℕ → ℝ) (hwtnn : ∀ T, 0 ≤ wt T)
    (lower upper : Dn → List HexBridge)
    (hlo : ∀ d, StrictDecreasingWidths (lower d))
    (hup : ∀ d, StrictDecreasingWidths (upper d))
    (htwoEdge : ∀ d, wtγ d * x ^ 2
        = ((lower d).map (fun b => wt b.width)).prod
          * ((upper d).map (fun b => wt b.width)).prod)
    (hdomLo : ∀ d, ∀ b ∈ lower d, wt b.width ≤ υ b.width)
    (hdomUp : ∀ d, ∀ b ∈ upper d, wt b.width ≤ υ b.width)
    (decomp_inj : Function.Injective
      (fun d => (hbw_widthFinset (lower d), hbw_widthFinset (upper d)))) :
    HexHWDataRecon c υ x N :=
  hexHWDataClosed c υ x N hυnn hmul Dn wtγ wtγ_nn partial_eq
    (fun d => (hbw_widthFinset (lower d), hbw_widthFinset (upper d)))
    decomp_inj
    (fun d => hbw_weightBound_factor x (wtγ d) hx (lower d) (upper d) (hlo d) (hup d)
      υ wt (hdomLo d) (hdomUp d) hwtnn (htwoEdge d))


end StatMech.Universality
