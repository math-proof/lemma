/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Def.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part8
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


@[simp]
theorem sctBoxMag_origin (d : ℕ) (β h : ℝ) (n : ℕ) :
    sctBoxMag d β h n (sctBoxOrigin d n) = sctOriginMag d β h n := rfl


theorem sctBoxMag_eq_translated_origin (d : ℕ) (β h : ℝ) (n : ℕ)
    (x : sctBox d n) :
    sctBoxMag d β h n x =
      isingExpectation (sctTranslatedBoxGraph d n x.1) β h
        (fun s => spin s (sctTranslateEquiv d n x.1 x)) := by
  exact isingExpectation_spin_relabel (sctBoxGraph d n)
    (sctTranslatedBoxGraph d n x.1) (sctTranslateEquiv d n x.1)
    (sctTranslateEquiv_adj d n x.1) β h x


theorem sctTranslateEquiv_self (d : ℕ) (n : ℕ) (x : sctBox d n) :
    (sctTranslateEquiv d n x.1 x).1 = (fun _ => 0 : Site d) := by
  funext i
  simp [sctTranslateEquiv]


theorem sctBoxMag_pos (d : ℕ) (β h : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (n : ℕ) (x : sctBox d n) :
    0 < sctBoxMag d β h n x :=
  sct_expectation_spin_pos (sctBoxGraph d n) β h hβ hh x


theorem sctOriginMag_pos (d : ℕ) (β h : ℝ) (hβ : 0 < β) (hh : 0 < h) (n : ℕ) :
    0 < sctOriginMag d β h n :=
  sctBoxMag_pos d β h hβ hh n (sctBoxOrigin d n)


theorem sctOriginMag_le_one (d : ℕ) (β h : ℝ) (n : ℕ) :
    sctOriginMag d β h n ≤ 1 :=
  expectation_spin_le_one (sctBoxGraph d n) β h (sctBoxOrigin d n)


theorem sctOriginMag_monotone (d : ℕ) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) : Monotone (sctOriginMag d β h) := by
  intro n m hnm
  let e := sctBoxInclusionEquiv d hnm
  calc
    sctOriginMag d β h n =
        isingExpectation
          ((sctBoxGraph d m).comap
            (Subtype.val :
              {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m)) β h
          (fun s => spin s (e (sctBoxOrigin d n))) := by
            exact isingExpectation_spin_relabel (sctBoxGraph d n)
              ((sctBoxGraph d m).comap
                (Subtype.val :
                  {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m))
              e (sctBoxInclusionEquiv_adj d hnm) β h (sctBoxOrigin d n)
    _ ≤ isingExpectation (sctBoxGraph d m) β h
          (fun s => spin s (e (sctBoxOrigin d n)).1) :=
      isingExpectation_spin_induce_le (sctBoxGraph d m)
        (sctBoxInLarger d n m) β h hβ hh (e (sctBoxOrigin d n))
    _ = sctOriginMag d β h m := by
      congr 2


theorem sctBoxMag_le_double (d : ℕ) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (n : ℕ) (x : sctBox d n) :
    sctBoxMag d β h n x ≤ sctOriginMag d β h (2 * n) := by
  let o := sctTranslateEquiv d n x.1 x
  let e := sctTranslatedInDoubleEquiv d n x
  calc
    sctBoxMag d β h n x =
        isingExpectation (sctTranslatedBoxGraph d n x.1) β h
          (fun s => spin s o) := sctBoxMag_eq_translated_origin d β h n x
    _ = isingExpectation
          ((sctBoxGraph d (2 * n)).comap
            (Subtype.val :
              {z : sctBox d (2 * n) // sctTranslatedInDouble d n x z} →
                sctBox d (2 * n))) β h
          (fun s => spin s (e o)) := by
            exact isingExpectation_spin_relabel (sctTranslatedBoxGraph d n x.1)
              ((sctBoxGraph d (2 * n)).comap
                (Subtype.val :
                  {z : sctBox d (2 * n) // sctTranslatedInDouble d n x z} →
                    sctBox d (2 * n)))
              e (sctTranslatedInDoubleEquiv_adj d n x) β h o
    _ ≤ isingExpectation (sctBoxGraph d (2 * n)) β h
          (fun s => spin s (e o).1) :=
      isingExpectation_spin_induce_le (sctBoxGraph d (2 * n))
        (sctTranslatedInDouble d n x) β h hβ hh (e o)
    _ = sctOriginMag d β h (2 * n) := by
      have hsite : (e o).1 = sctBoxOrigin d (2 * n) := by
        ext i
        exact congrFun (sctTranslateEquiv_self d n x) i
      rw [hsite]
      rfl


theorem sctLatticeC_le_one (d : ℕ) (β h : ℝ) (hβ : 0 < β) (hh : 0 < h) (n : ℕ) :
    sctLatticeC d β h n ≤ 1 := by
  unfold sctLatticeC
  exact sct_cInfDep_le_one (sctBox d) (sctOriginMag d β h) (sctBoxSites d)
    (sctBoxMag d β h) (sctBoxSites_nonempty d) (sctBoxOrigin d)
    (fun k => Finset.mem_univ _) (sctBoxMag_origin d β h)
    (fun k => (sctOriginMag_pos d β h hβ hh k).ne') n


theorem sctLatticeC_tendsto_one (d : ℕ) (β h : ℝ) (hβ : 0 < β) (hh : 0 < h)
    :
    Tendsto (sctLatticeC d β h) atTop (𝓝 1) := by
  exact sct_cInfDep_to_one_of_monotone (sctBox d) (sctOriginMag d β h)
    (sctBoxSites d) (sctBoxMag d β h) (sctBoxSites_nonempty d)
    (sctOriginMag_monotone d β h hβ.le hh.le)
    (sctOriginMag_le_one d β h) (sctOriginMag_pos d β h hβ hh 0)
    (fun n x _ => sctBoxMag_pos d β h hβ hh n x) (sctBoxOrigin d)
    (fun n => Finset.mem_univ _) (sctBoxMag_origin d β h)
    (fun n x _ => sctBoxMag_le_double d β h hβ.le hh.le n x)

end Sharpness
end StatMech
