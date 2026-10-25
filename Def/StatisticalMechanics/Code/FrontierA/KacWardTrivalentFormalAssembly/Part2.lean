/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardTrivalentCoefficients
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalCoefficient.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardTrivalentFormalAssembly
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager

universe u


def KWGraphUnitCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) : Prop :=
  (∀ {root : V} (p : G.Walk root root), p.IsCycle →
      kwGraphFormalLogCoeff G phase
        (ons_finsetExponent p.edges.toFinset) = 1) ∧
  (∀ (S : Finset (Sym2 V)),
      kwGraphFormalLogCoeff G phase (ons_finsetExponent S) ≠ 0 →
        ∃ (root : V) (p : G.Walk root root),
          p.IsCycle ∧ p.edges.toFinset = S)


noncomputable def kwCycleComponentSeries
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I → V)
    (cycle : (i : I) → G.Walk (base i) (base i)) :
    MvPowerSeries (Sym2 V) ℂ :=
  ∑ i : I, MvPowerSeries.monomial
    (ons_finsetExponent (cycle i).edges.toFinset) 1

end StatMech.FrontierA
