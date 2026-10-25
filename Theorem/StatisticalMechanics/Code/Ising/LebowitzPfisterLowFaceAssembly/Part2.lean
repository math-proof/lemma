/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part2
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

lemma bernsteinWeight_nonneg {n i : Nat} {x : Real}
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    0 <= bernsteinWeight n i x := by
  unfold bernsteinWeight
  positivity

set_option maxHeartbeats 800000 in
lemma scaledBernFactor_sum_twelve (e : Nat) (he : e <= 6) (x : Real) :
    ∑ i : Fin 13,
      (scaledBernFactor 12 27720 e i : Real) * bernsteinWeight 12 i x =
      27720 * x ^ e := by
  interval_cases e <;>
    norm_num [Fin.sum_univ_succ, scaledBernFactor, bernsteinWeight, Nat.choose] <;>
    ring

set_option maxHeartbeats 800000 in
lemma scaledBernFactor_sum_seven (e : Nat) (he : e <= 6) (x : Real) :
    ∑ i : Fin 8,
      (scaledBernFactor 7 105 e i : Real) * bernsteinWeight 7 i x =
      105 * x ^ e := by
  interval_cases e <;>
    norm_num [Fin.sum_univ_succ, scaledBernFactor, bernsteinWeight, Nat.choose] <;>
    ring

set_option maxHeartbeats 800000 in
lemma scaledBernFactor_sum_three (e : Nat) (he : e <= 3) (x : Real) :
    ∑ i : Fin 4,
      (scaledBernFactor 3 3 e i : Real) * bernsteinWeight 3 i x =
      3 * x ^ e := by
  interval_cases e <;>
    norm_num [Fin.sum_univ_succ, scaledBernFactor, bernsteinWeight, Nat.choose] <;>
    ring

end LowFaceCertificate
end
end StatMech.Ising
