/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSharpnessFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

section Claim2Consumption

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem localized_two_point_of_claim2 (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (g : V)
    (hg : g ∉ S) (zero x : V) (h0 : zero ∈ S) (hx : x ∈ S)
    (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0)
    (hden : (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0)) ≠ 0) :
    expectationJ G β (couplingIn J S) {zero, x}
      = (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = {zero, x} then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0))
        / (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0)) := by
  rw [claim2_ising G β J S g hg zero x h0 hx hZ, mul_div_assoc, div_self hden, mul_one]

end Claim2Consumption
end Sharpness
end StatMech
