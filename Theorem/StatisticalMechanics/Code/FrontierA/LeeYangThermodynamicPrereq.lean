/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangThermodynamicPrereq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangBoxPressure.Part3
open scoped BigOperators
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FK StatMech.FrontierB StatMech.FrontierC
  StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteFerromagneticLeeYang_headline {beta : ℝ} (hbeta : 0 ≤ beta) :
    (∀ z : ℂ, (leeYangComplexPolynomial G beta).eval z = 0 → ‖z‖ = 1) ∧
    (∀ z : ℂ, ‖z‖ ≠ 1 → (leeYangComplexPolynomial G beta).eval z ≠ 0) ∧
    (∀ h : ℂ, h.re ≠ 0 → leeYangComplexFieldPartition G beta h ≠ 0) ∧
    ∀ f : ConfigSpace V → ℂ,
      AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f)
        {h : ℂ | h.re ≠ 0} := by
  refine ⟨finiteGraph_hasLeeYangCircle G hbeta, ?_, ?_, ?_⟩
  · intro z hz
    exact leeYangComplexPolynomial_ne_zero_of_norm_ne_one G hbeta hz
  · intro h hh
    exact leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero G hbeta hh
  · intro f
    exact leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero G hbeta f

end StatMech.FrontierA
