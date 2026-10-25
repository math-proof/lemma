/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part36
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwDartPortSplit_weightedEnumerator_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : KWDartEdgeBits G → ℂ) :
    (∑ b : KWOriginalEvenBits G, W b.1) =
      ∑ p : KWSplitEvenBits G, W p.1.1 := by
  classical
  apply Fintype.sum_equiv (kwDartPortSplitEvenEquiv G)
  intro b
  rfl


theorem kw_det_portSplit_of_effective_gauge
    {External Internal : Type*}
    [Fintype External] [DecidableEq External]
    [Fintype Internal] [DecidableEq Internal]
    (original external : Matrix External External ℂ)
    (enter : Matrix External Internal ℂ)
    (exit : Matrix Internal External ℂ)
    (internal : Matrix Internal Internal ℂ)
    (nilpotenceIndex : ℕ) (hpow : internal ^ nilpotenceIndex = 0)
    (gauge : External → ℂ) (hgauge : ∀ i, gauge i ≠ 0)
    (heffective :
      kwEliminateAcyclicInternal external enter exit internal
          nilpotenceIndex = kwGaugeConjugate gauge original) :
    (1 - kwInternalGadgetTransition external enter exit internal).det =
      (1 - original).det := by
  rw [kw_det_eliminateAcyclicInternal external enter exit internal
      nilpotenceIndex hpow,
    heffective, kw_det_one_sub_gaugeConjugate gauge original hgauge]

end StatMech.FrontierA
