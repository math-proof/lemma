/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorRows.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldOpenBoundaryCrossover
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorMeasureClosure.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorRows
open Filter MeasureTheory Set


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

noncomputable def finiteDeepConnectorBandSchedule_of_separatedRows
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (rDual : Real) (band : Nat)
    {r R : Real} (hrR : r ≤ R) (s : Real) (t : Int)
    (hdisjoint : ∀ (L U : Finset V) (width : Nat),
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      U = L.image (P.shift (verticalShift (1 + t))) →
      Disjoint
        (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
          r R s (s + t) width L U)
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
            rDual (-(band : Real)) band)) :
    D.FiniteDeepConnectorBandSchedule mu rDual band := by
  let epsilon : Nat → Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hrow (n : Nat) : ∃ L U : Finset V, ∃ width : Nat,
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R ∧
      (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R ∧
      U = L.image (P.shift (verticalShift (1 + t))) ∧
      1 - 2 * Real.sqrt
          (1 - (mu.real (P.orbitBoxHitsInfinite n)) ^ 2) -
          3 * epsilon n <
        mu.real
          (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
            r R s (s + t) width L U) :=
    D.primalEmbedding.exists_separated_finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_gt
      mu hFKG hTI hunique hrR s t n (hepsilon n)
  choose lower upper width hlowerDeep hupperDeep htranslate hmass using hrow
  refine
    { rPrimal := fun _ => r
      Rdeep := fun _ => R
      cArm := fun _ => s
      dArm := fun _ => s + t
      width := width
      lower := lower
      upper := upper
      tendsto_one := ?_
      disjoint_band := fun n =>
        hdisjoint (lower n) (upper n) (width n)
          (hlowerDeep n) (hupperDeep n) (htranslate n) }
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hsq : Tendsto (fun n : Nat =>
      (mu.real (P.orbitBoxHitsInfinite n)) ^ 2) atTop (nhds 1) := by
    simpa using hbox.pow 2
  have hmiss : Tendsto (fun n : Nat =>
      1 - (mu.real (P.orbitBoxHitsInfinite n)) ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hsq
  have hsqrt : Tendsto (fun n : Nat => Real.sqrt
      (1 - (mu.real (P.orbitBoxHitsInfinite n)) ^ 2))
      atTop (nhds 0) := by
    simpa using hmiss.sqrt
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    simpa only [epsilon, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlowerLimit : Tendsto (fun n : Nat =>
      1 - 2 * Real.sqrt
          (1 - (mu.real (P.orbitBoxHitsInfinite n)) ^ 2) -
        3 * epsilon n) atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : Real))).sub
        (hsqrt.const_mul 2)).sub (hepsilonZero.const_mul 3)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlowerLimit tendsto_const_nhds
      (fun n => (hmass n).le) (fun _ => measureReal_le_one)


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
