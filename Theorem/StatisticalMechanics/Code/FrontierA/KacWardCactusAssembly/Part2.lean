/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCactusAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnicyclicAssembly.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardCactusAssembly.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


theorem kacWard_abstract_cactus_of_phase_sign
    {E Block : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    [Fintype Block] [DecidableEq Block] [LinearOrder Block]
    (sigma : Block -> Equiv.Perm E)
    (edgeWeight : Block -> E -> ℂ)
    (phase : Block -> Bool -> E -> ℂ)
    (forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ)
    (hforward : kwStrictlyForward forward)
    (hcycle : ∀ b, (sigma b).IsCycle)
    (hfree : ∀ b i, sigma b i ≠ i)
    (hphase : ∀ b o, ∏ i, phase b o i = -1) :
    (1 - kwCycleFamilyExtension sigma
        (fun b o i => edgeWeight b i * phase b o i) forward).det =
      (kwAbstractCactusEvenPolynomial edgeWeight) ^ 2 := by
  rw [kw_det_cycleFamilyExtension sigma _ forward hforward]
  have hblock : ∀ b,
      (1 - kwTwoOrientationCycleTransition (sigma b)
        (fun o i => edgeWeight b i * phase b o i)).det =
        (kwAbstractCycleEvenPolynomial (edgeWeight b)) ^ 2 := by
    intro b
    exact kacWard_abstract_cycle_of_phase_sign (sigma b) (edgeWeight b)
      (phase b) (hcycle b) (hfree b) (hphase b)
  simp_rw [hblock]
  unfold kwAbstractCactusEvenPolynomial
  rw [Finset.prod_pow]

end StatMech.FrontierA
