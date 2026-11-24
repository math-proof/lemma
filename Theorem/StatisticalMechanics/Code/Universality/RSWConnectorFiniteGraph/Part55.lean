module
public import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
public import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part73
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCollaredOuterDualEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_connectorCollaredOuterDualEdge gamma gamma') := by
  intro f g hfg
  unfold rlc_connectorCollaredOuterDualEdge at hfg
  split at hfg <;> split at hfg
  · rename_i hf hg
    have hedge : hf.choose.1 = hg.choose.1 := by
      apply Sym2.map.injective
        (rlc_connectorCollaredOuterTargetVertex_injective gamma gamma')
      exact hfg
    apply rlc_connectorReflectedDualEdge_injective gamma gamma'
    rw [← hf.choose_spec, ← hg.choose_spec, hedge]
  · rename_i hf hg
    revert hfg
    induction hf.choose.1 using Sym2.inductionOn with
    | _ x y =>
        intro hfg
        rw [Sym2.map_mk, Sym2.eq_iff] at hfg
        simp [rlc_connectorCollaredOuterTargetVertex,
          rlc_connectorCollaredOuterPort] at hfg
  · rename_i hf hg
    revert hfg
    induction hg.choose.1 using Sym2.inductionOn with
    | _ x y =>
        intro hfg
        rw [Sym2.map_mk, Sym2.eq_iff] at hfg
        simp [rlc_connectorCollaredOuterTargetVertex,
          rlc_connectorCollaredOuterPort] at hfg
  · simpa [rlc_connectorCollaredOuterPort, Sym2.eq_iff] using hfg


end
end StatMech.Universality
