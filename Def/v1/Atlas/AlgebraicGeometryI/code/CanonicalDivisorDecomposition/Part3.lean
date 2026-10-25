/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Mathlib.RingTheory.DedekindDomain.Different
import Theorem.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition


noncomputable section

open Ideal Module CanonicalSheafCurves

section GlobalRamification

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S]

attribute [instance] CurveCovering.instCR CurveCovering.instDR
  CurveCovering.instCS CurveCovering.instDS CurveCovering.instAlg
  CurveCovering.instNZ

section TrivialCovering

open CanonicalSheafCurves

/-- Trivial identity covering of an elliptic curve by itself (degree 1, no ramification). -/
def CurveCovering.ellipticIdentity : CurveCovering where
  R := ℤ
  S := ℤ
  X := mkCurve 1
  Y := mkCurve 1
  n := 1
  h_n_pos := Int.one_pos
  basePrimes := ∅
  h_max := fun _ h => absurd h (by simp)
  h_bot := fun _ h => absurd h (by simp)
  localDegK_X := fun _ => 0
  localDegK_Y := fun _ => 0
  h_degK_X_sum := by simp [mkCurve]
  h_degK_Y_sum := by simp [mkCurve]
  h_local_degree := fun _ h => absurd h (by simp)

/-- Identity covering of `P^1` by itself, using a prescribed prime `p` of `ℤ` with vanishing
total ramification. -/
def CurveCovering.P1Identity
    (p : Ideal ℤ) (hp_max : p.IsMaximal) (hp_bot : p ≠ ⊥)
    (h_totalRam : totalRamificationAt ℤ p hp_bot = 0) :
    CurveCovering where
  R := ℤ
  S := ℤ
  X := mkCurve 0
  Y := mkCurve 0
  n := 1
  h_n_pos := Int.one_pos
  basePrimes := {p}
  h_max := by simp [hp_max]
  h_bot := by simp [hp_bot]
  localDegK_X := fun q => if q = p then -2 else 0
  localDegK_Y := fun q => if q = p then -2 else 0
  h_degK_X_sum := by simp [mkCurve]
  h_degK_Y_sum := by simp [mkCurve]
  h_local_degree := by
    intro q hq
    simp only [Finset.mem_singleton] at hq
    subst hq
    simp only [ite_true, dif_pos (Finset.mem_singleton.mpr rfl)]

    rw [h_totalRam]
    ring

/-- General identity covering: a smooth complete curve `C` paired with itself at degree `1`. -/
def CurveCovering.identityCovering
    (C : SmoothCompleteCurve)
    (p : Ideal ℤ) (hp_max : p.IsMaximal) (hp_bot : p ≠ ⊥)
    (h_totalRam : totalRamificationAt ℤ p hp_bot = 0) :
    CurveCovering where
  R := ℤ
  S := ℤ
  X := C
  Y := C
  n := 1
  h_n_pos := Int.one_pos
  basePrimes := {p}
  h_max := by simp [hp_max]
  h_bot := by simp [hp_bot]
  localDegK_X := fun q => if q = p then C.degK else 0
  localDegK_Y := fun q => if q = p then C.degK else 0
  h_degK_X_sum := by simp
  h_degK_Y_sum := by simp
  h_local_degree := by
    intro q hq
    simp only [Finset.mem_singleton] at hq
    subst hq
    simp only [ite_true, dif_pos (Finset.mem_singleton.mpr rfl)]
    rw [h_totalRam]
    ring

end TrivialCovering
end GlobalRamification
end
