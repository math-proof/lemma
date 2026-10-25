/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose.Part2
import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part6
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_boxRColour_sidesConnected
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
    Ising.kwg_ColourSidesConnected (crr_boxPlanar n).G (crr_boxRColour omega n) := by
  classical
  intro b x y
  cases b with
  | false =>
      have hxNotR : x.1.1 ∉ bac_rightComplement omega n := by
        simpa [crr_boxRColour] using x.2
      have hyNotR : y.1.1 ∉ bac_rightComplement omega n := by
        simpa [crr_boxRColour] using y.2
      have hxFill : x.1.1 ∈ crr_leftFill omega n := ⟨x.1.2, hxNotR⟩
      have hyFill : y.1.1 ∈ crr_leftFill omega n := ⟨y.1.2, hyNotR⟩
      have hxy := crr_leftFill_connected_pair omega n hxFill hyFill
      let phi : ((hypercubicLattice 2).induce (crr_leftFill omega n)) →g
          ((crr_boxPlanar n).G.induce {v | crr_boxRColour omega n v = false}) := {
        toFun := fun (z : crr_leftFill omega n) =>
          (⟨(⟨z.1, z.2.1⟩ : (crr_boxPlanar n).V),
            by simp [crr_boxRColour, z.2.2]⟩ :
            {v : (crr_boxPlanar n).V // crr_boxRColour omega n v = false})
        map_rel' := by
          intro a b hab
          exact hab }
      have hm := hxy.map phi
      convert hm using 1 <;> rfl
  | true =>
      have hxR : x.1.1 ∈ bac_rightComplement omega n := by
        simpa [crr_boxRColour] using x.2
      have hyR : y.1.1 ∈ bac_rightComplement omega n := by
        simpa [crr_boxRColour] using y.2
      have hxy := crr_rightComplement_connected_induced omega n hnoH hxR hyR
      let phi : ((hypercubicLattice 2).induce (bac_rightComplement omega n)) →g
          ((crr_boxPlanar n).G.induce {v | crr_boxRColour omega n v = true}) := {
        toFun := fun (z : bac_rightComplement omega n) =>
          (⟨(⟨z.1, (bac_rightComplement_mem omega n z.2).1⟩ :
              (crr_boxPlanar n).V), by simp [crr_boxRColour, z.2]⟩ :
            {v : (crr_boxPlanar n).V // crr_boxRColour omega n v = true})
        map_rel' := by
          intro a b hab
          exact hab }
      have hm := hxy.map phi
      convert hm using 1 <;> rfl


theorem crr_boxR_dualEven_subset_eq
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n)
    (F : Finset (Ising.kwg_Edge (crr_boxPlanar n)))
    (hsub : F ⊆ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
      (crr_boxRColour omega n))
    (hne : F.Nonempty)
    (heven : Ising.kwg_IsEven (Ising.kwg_dualEnds (crr_boxPlanar n)) F) :
    F = Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
      (crr_boxRColour omega n) :=
  Ising.kwg_dualEven_subset_bond_eq (crr_boxPlanar n) (crr_boxRColour omega n)
    (crr_boxRColour_sidesConnected omega n hnoH) F hsub hne heven


end Universality
end StatMech
