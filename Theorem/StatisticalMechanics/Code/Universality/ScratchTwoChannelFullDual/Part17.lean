/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part19
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelIndexedAugmentedEdge_reflected {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    rlc_twoChannelReflectedDualEdge gamma gamma'
        (rlc_twoChannelIndexedAugmentedEdge target) =
      target.1.map Subtype.val := by
  apply rlc_pimsEdgeEquiv.injective
  rw [rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge]
  change (rlc_twoChannelFullSourceEdge target).1.map Subtype.val =
    rlc_pimsEdgeEquiv (target.1.map Subtype.val)
  exact rlc_twoChannelFullSourceEdge_map target

theorem rlc_twoChannelIndexedOuterEdge_variable {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    rlc_twoChannelIndexedOuterEdge gamma gamma'
        (rlc_twoChannelIndexedAugmentedEdge target) =
      target.1.map (rlc_twoChannelIndexedOuterTarget gamma gamma') := by
  have hret : RlcTwoChannelIndexedRetainedEdge gamma gamma'
      (rlc_twoChannelIndexedAugmentedEdge target) :=
    ⟨target, (rlc_twoChannelIndexedAugmentedEdge_reflected target).symm⟩
  unfold rlc_twoChannelIndexedOuterEdge
  rw [dif_pos hret]
  have hedge : hret.choose.1 = target.1 := by
    apply Sym2.map.injective Subtype.val_injective
    exact hret.choose_spec.trans
      (rlc_twoChannelIndexedAugmentedEdge_reflected target)
  exact congrArg (Sym2.map
    (rlc_twoChannelIndexedOuterTarget gamma gamma')) hedge

theorem rlc_twoChannelIndexedOuterEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_twoChannelIndexedOuterEdge gamma gamma') := by
  intro f g hfg
  unfold rlc_twoChannelIndexedOuterEdge at hfg
  split at hfg <;> split at hfg
  · rename_i hf hg
    have hedge : hf.choose.1 = hg.choose.1 := by
      apply Sym2.map.injective
        (rlc_twoChannelIndexedOuterTarget_injective gamma gamma')
      exact hfg
    apply rlc_twoChannelReflectedDualEdge_injective gamma gamma'
    rw [← hf.choose_spec, ← hg.choose_spec, hedge]
  · rename_i hf hg
    revert hfg
    induction hf.choose.1 using Sym2.inductionOn with
    | _ x y =>
        intro hfg
        rw [Sym2.map_mk, Sym2.eq_iff] at hfg
        simp [rlc_twoChannelIndexedOuterTarget,
          rlc_twoChannelIndexedOuterPort] at hfg
  · rename_i hf hg
    revert hfg
    induction hg.choose.1 using Sym2.inductionOn with
    | _ x y =>
        intro hfg
        rw [Sym2.map_mk, Sym2.eq_iff] at hfg
        simp [rlc_twoChannelIndexedOuterTarget,
          rlc_twoChannelIndexedOuterPort] at hfg
  · simpa [rlc_twoChannelIndexedOuterPort, Sym2.eq_iff] using hfg

end
end StatMech.Universality
