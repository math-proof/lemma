/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteBoundaryCutoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteCutoff
import Mathlib.Combinatorics.SimpleGraph.Metric
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFiniteBoundaryCutoff.Part3


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

theorem isingFiniteGraphBoundaryTentCutoff_support
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (r : Nat) :
    ∀ x, isingFiniteGraphBoundaryTentCutoff G boundary hboundary r x ≠ 0 →
      ¬ boundary x := by
  intro x hx hxb
  have hzero := isingFiniteGraphDistanceToBoundary_eq_zero
    G boundary hboundary x hxb
  simp [isingFiniteGraphBoundaryTentCutoff, hzero] at hx

theorem isingFiniteGraphBoundaryTentCutoff_lipschitz
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (r : Nat) (hr : 0 < r)
    (d : G.Dart) :
    |isingFiniteGraphBoundaryTentCutoff G boundary hboundary r d.snd -
      isingFiniteGraphBoundaryTentCutoff G boundary hboundary r d.fst| ≤
        1 / (r : Real) := by
  let rho := isingFiniteGraphDistanceToBoundary G boundary hboundary
  have hdistNat := isingFiniteGraphDistanceToBoundary_adj
    G boundary hboundary d.2
  have hdist : |(rho d.snd : Real) - (rho d.fst : Real)| ≤ 1 := by
    have hforward : (rho d.snd : Real) ≤ (rho d.fst : Real) + 1 := by
      exact_mod_cast hdistNat.1
    have hbackward : (rho d.fst : Real) ≤ (rho d.snd : Real) + 1 := by
      exact_mod_cast hdistNat.2
    rw [abs_le]
    constructor <;> linarith
  have hmin := abs_min_sub_min_le_max (1 : Real)
    ((rho d.snd : Real) / (r : Real)) 1
    ((rho d.fst : Real) / (r : Real))
  calc
    _ ≤ |(rho d.snd : Real) / (r : Real) -
        (rho d.fst : Real) / (r : Real)| := by
      simpa [isingFiniteGraphBoundaryTentCutoff, rho] using hmin
    _ = |(rho d.snd : Real) - (rho d.fst : Real)| / (r : Real) := by
      rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : Real) < r)]
    _ ≤ 1 / (r : Real) := by
      exact div_le_div_of_nonneg_right hdist (by positivity)

theorem isingFiniteGraphBoundaryTentCutoff_eq_one
    {V : Type*} [Fintype V] (G : SimpleGraph V) (boundary : V → Prop)
    (hboundary : ∃ x, boundary x) (r : Nat) (hr : 0 < r) (x : V)
    (hx : r ≤ isingFiniteGraphDistanceToBoundary G boundary hboundary x) :
    isingFiniteGraphBoundaryTentCutoff G boundary hboundary r x = 1 := by
  unfold isingFiniteGraphBoundaryTentCutoff
  rw [min_eq_left]
  apply (le_div_iff₀' (by positivity : (0 : Real) < r)).2
  norm_num
  exact_mod_cast hx

end
end StatMech.Universality
