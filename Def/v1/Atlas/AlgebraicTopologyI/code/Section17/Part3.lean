/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section17


noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- The chain-level homology of $\mathbf{RP}^n$ matches the explicit description in
`homologyGroup`. -/
def rpnChainHomology_iso_homologyGroup (n k : ℕ) :
    rpnChainHomology n k ≅ homologyGroup n k := by
  unfold rpnChainHomology homologyGroup
  by_cases hkn : n < k
  ·
    simp only [show k > n from hkn, ite_true]
    simp only [show k ≠ 0 from by omega, show ¬(k = n ∧ Odd n) from by omega,
      show ¬(Odd k ∧ k < n) from by omega, ite_false]
    exact Iso.refl _
  ·
    simp only [show ¬(k > n) from by omega, ite_false]
    by_cases hk0 : k = 0
    ·
      subst hk0; simp only [ite_true]; rw [rpnImageSubgroup_zero]
      exact AddEquiv.toAddCommGrpIso QuotientAddGroup.quotientBot
    · simp only [hk0, ite_false]
      by_cases hkodd : Odd k
      ·
        simp only [hkodd, ite_true]
        by_cases hkeqn : k = n
        ·
          subst hkeqn; simp only [true_and, hkodd, ite_true]
          rw [rpnImageSubgroup_self]
          exact AddEquiv.toAddCommGrpIso QuotientAddGroup.quotientBot
        ·
          have hklt : k < n := by omega
          simp only [show ¬(k = n) from hkeqn, false_and, ite_false, hklt, and_self, ite_true]
          rw [rpnImageSubgroup_odd_lt hkodd hklt]
          exact AddEquiv.toAddCommGrpIso (Int.quotientZMultiplesNatEquivZMod 2)
      ·
        simp only [hkodd, ite_false]
        simp only [show ¬(k = n ∧ Odd n) from fun ⟨h, ho⟩ => by subst h; exact hkodd ho,
          ite_false]
        exact Iso.refl _

/-- The antipodal map $x \mapsto -x$ on $S^n$. -/
def sphereNeg (n : ℕ) (x : Sphere n) : Sphere n :=
  ⟨-↑x, by
    have hx := x.2
    simp only [Metric.mem_sphere, dist_zero_right] at hx ⊢
    rw [norm_neg]; exact hx⟩

end RealProjectiveSpace
end
