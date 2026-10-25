/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Mathlib.GroupTheory.Perm.Fin
import Def.StatisticalMechanics.Code.FrontierA.KacWardCycleAssembly.Part3
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open Matrix

open StatMech.Onsager StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.GeneralUmlaufsatz


theorem kacWard_abstract_cycle_of_phase_sign
    {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    (sigma : Equiv.Perm E) (edgeWeight : E -> ℂ)
    (phase : Bool -> E -> ℂ)
    (hcycle : sigma.IsCycle) (hfree : ∀ i, sigma i ≠ i)
    (hphase : ∀ b, ∏ i, phase b i = -1) :
    (1 - kwTwoOrientationCycleTransition sigma
        (fun b i => edgeWeight i * phase b i)).det =
      (kwAbstractCycleEvenPolynomial edgeWeight) ^ 2 := by
  rw [kw_det_twoOrientationCycle sigma _ hcycle hfree]
  have hweight : ∀ b,
      ∏ i, edgeWeight i * phase b i = -(∏ i, edgeWeight i) := by
    intro b
    rw [Finset.prod_mul_distrib, hphase b]
    ring
  rw [hweight false, hweight true]
  unfold kwAbstractCycleEvenPolynomial
  ring


theorem kw_finRotate_free {n : ℕ} (hn : 2 ≤ n) :
    ∀ i : Fin n, finRotate n i ≠ i := by
  have hsupport := support_finRotate_of_le hn
  intro i
  exact Equiv.Perm.mem_support.mp (by rw [hsupport]; exact Finset.mem_univ i)


theorem kacWard_rectilinear_cycle
    {n : ℕ} [NeZero n]
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (d : Fin n -> Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (hnu : ∀ i, d (i + 1) ≠ d i + 2)
    (edgeWeight : Fin n -> ℂ) :
    (1 - kwTwoOrientationCycleTransition (finRotate n)
        (fun _ i => edgeWeight i * ons_turnW omega (d i) (d (i + 1)))).det =
      (kwAbstractCycleEvenPolynomial edgeWeight) ^ 2 := by
  apply kacWard_abstract_cycle_of_phase_sign
      (finRotate n) edgeWeight
      (fun _ i => ons_turnW omega (d i) (d (i + 1)))
  · exact isCycle_finRotate_of_le (by omega)
  · exact kw_finRotate_free (by omega)
  · intro _
    exact turnWeightProduct_eq_neg_one omega homega hI d
      hclosed hsimple hn hnu

end StatMech.FrontierA
