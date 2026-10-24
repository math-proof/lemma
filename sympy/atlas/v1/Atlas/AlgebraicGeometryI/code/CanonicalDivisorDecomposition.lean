/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
import Mathlib.RingTheory.DedekindDomain.Different

noncomputable section

open Ideal Module CanonicalSheafCurves

section GlobalRamification

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S]

/-- Global ramification contribution: sum of the total ramification at each prime of `R` lying
under the cover `S/R`. -/
def globalRamification
    (basePrimes : Finset (Ideal R))
    (hmax : ∀ p ∈ basePrimes, p.IsMaximal)
    (hbot : ∀ p ∈ basePrimes, p ≠ ⊥) : ℤ :=
  basePrimes.sum fun p =>
    if h : p ∈ basePrimes then
      haveI : p.IsMaximal := hmax p h
      totalRamificationAt S p (hbot p h)
    else 0

/-- Data of a finite covering of smooth complete curves `X → Y` arising from a Dedekind ring
extension `R ⊂ S`, together with the local canonical-degree decompositions used in the
Riemann–Hurwitz formula. -/
structure CurveCovering where
  R : Type*
  S : Type*
  [instCR : CommRing R]
  [instDR : IsDedekindDomain R]
  [instCS : CommRing S]
  [instDS : IsDedekindDomain S]
  [instAlg : Algebra R S]
  [instNZ : NoZeroSMulDivisors R S]
  X : SmoothCompleteCurve
  Y : SmoothCompleteCurve
  n : ℤ
  h_n_pos : 0 < n
  basePrimes : Finset (Ideal R)
  h_max : ∀ p ∈ basePrimes, p.IsMaximal
  h_bot : ∀ p ∈ basePrimes, p ≠ ⊥
  localDegK_X : Ideal R → ℤ
  localDegK_Y : Ideal R → ℤ
  h_degK_X_sum : X.degK = basePrimes.sum localDegK_X
  h_degK_Y_sum : Y.degK = basePrimes.sum localDegK_Y
  h_local_degree : ∀ p ∈ basePrimes,
    localDegK_X p = n * localDegK_Y p +
      (if h : p ∈ basePrimes then
        haveI : p.IsMaximal := h_max p h
        totalRamificationAt S p (h_bot p h)
      else 0)

attribute [instance] CurveCovering.instCR CurveCovering.instDR
  CurveCovering.instCS CurveCovering.instDS CurveCovering.instAlg
  CurveCovering.instNZ

section GlobalFormula

variable (f : CurveCovering)

/-- The ramification degree `deg R` of a curve covering. -/
def CurveCovering.deg_R : ℤ :=
  globalRamification f.S f.basePrimes f.h_max f.h_bot

example : (2 : ℤ) * 1 - 2 = 2 * (2 * 0 - 2) + 4 := by norm_num

example : (2 : ℤ) * 2 - 2 = 2 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 1 - 2 = 3 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

end Specializations

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

/-- Simplified curve-covering structure: stores only the global canonical-degree formula
without local data. -/
structure CurveCoveringDirect where
  R : Type*
  S : Type*
  [instCR : CommRing R]
  [instDR : IsDedekindDomain R]
  [instCS : CommRing S]
  [instDS : IsDedekindDomain S]
  [instAlg : Algebra R S]
  [instNZ : NoZeroSMulDivisors R S]
  X : SmoothCompleteCurve
  Y : SmoothCompleteCurve
  n : ℤ
  h_n_pos : 0 < n
  basePrimes : Finset (Ideal R)
  h_max : ∀ p ∈ basePrimes, p.IsMaximal
  h_bot : ∀ p ∈ basePrimes, p ≠ ⊥
  h_degK_formula :
    X.degK = n * Y.degK + globalRamification S basePrimes h_max h_bot

attribute [instance] CurveCoveringDirect.instCR CurveCoveringDirect.instDR
  CurveCoveringDirect.instCS CurveCoveringDirect.instDS
  CurveCoveringDirect.instAlg CurveCoveringDirect.instNZ

/-- Ramification degree of a `CurveCoveringDirect`. -/
def CurveCoveringDirect.deg_R (f : CurveCoveringDirect) : ℤ :=
  globalRamification f.S f.basePrimes f.h_max f.h_bot

/-- Forgetful map from the local `CurveCovering` data to the simpler `CurveCoveringDirect`. -/
def CurveCovering.toDirect (f : CurveCovering) : CurveCoveringDirect where
  R := f.R
  S := f.S
  X := f.X
  Y := f.Y
  n := f.n
  h_n_pos := f.h_n_pos
  basePrimes := f.basePrimes
  h_max := f.h_max
  h_bot := f.h_bot
  h_degK_formula := f.degK_eq

end DirectCovering

end
