/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part2


namespace StatMech.Universality

open Complex HexWalk Set


def hexEmptyIncidencePairing
    (R : HexFiniteRegion) (h0 : ℤ) :
    (hexEmptyIncidenceDomain R h0).InteriorPairing where
  interior := ∅
  pair := id
  pair_mem := by simp
  pair_invol := by simp
  pair_ne := by simp
  cancel := by simp


def hexEmptyIncidenceSides (R : HexFiniteRegion) : HexContourSides where
  bottom := ∅
  slantPlus := ∅
  slantMinus := ∅
  top := {R.start}


noncomputable def hexEmptyIncidenceBoundaryData
    (R : HexFiniteRegion) (h0 : ℤ) :
    HexFiniteStripBoundaryData R h0
      (hexEmptyIncidenceDomain R h0) (hexEmptyIncidencePairing R h0) where
  sides := hexEmptyIncidenceSides R
  interior_sub := by simp [hexEmptyIncidencePairing]
  vertex_mem := by
    intro v
    exact Fin.elim0 v
  mid_mem := by
    intro e he
    simp at he
  obs_eq := by
    intro z
    rfl
  lam := 0
  tau := 0
  ups := hexChi
  Fa := hexChi
  lam_eq := by
    simp [hexContourLambda, hexEmptyIncidenceSides, hexContourSum_empty]
  tau_eq := by
    simp [hexContourTauPlus, hexContourTauMinus, hexEmptyIncidenceSides,
      hexContourSum_empty]
  ups_eq := by
    simp only [hexContourUpsilon, hexEmptyIncidenceSides]
    exact (hexContourSum_singleton_start R.inRegion R.start h0 hexChi
      (by simpa [HexFiniteRegion.inRegion] using R.start_mem)).symm
  Fa_eq := by
    change (hexChi : ℂ) = parafObservable R.inRegion R.start h0 R.start
      (5 / 8) hexChi
    symm
    exact parafObservable_start_eq_weight R.inRegion R.start h0
      (5 / 8) hexChi (by simpa [HexFiniteRegion.inRegion] using R.start_mem)
  alphaRest := 0
  alphaRest_eq := by simp
  betaSum := hexChi
  betaSum_eq := rfl
  epsSum := 0
  epsSum_eq := by simp
  epsbarSum := 0
  epsbarSum_eq := by simp
  contour_eq := by
    simp [HexDomain.boundarySum, hexEmptyIncidencePairing,
      hexFiniteStripRaw]


end StatMech.Universality
