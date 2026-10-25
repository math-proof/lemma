/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry.Part3
import Theorem.StatisticalMechanics.Code.Walls.binsclosure.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation StatMech.Walls


def zbd_geometricData_of_twoScale
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (L R : ℕ → Set (Site 2)) (M : ℕ → ℕ)
    (hbaseInc : ∀ n, IsIncreasing (zbd_sideHasInfinite (L n)))
    (hbaseM : ∀ n, MeasurableSet (zbd_sideHasInfinite (L n)))
    (hopp : ∀ n,
      zrs_sideFamily (zbd_sideHasInfinite (L n)) 1 = zbd_sideHasInfinite (R n))
    (herr : Tendsto (fun n =>
      halfMeasure.real (zbd_twoScaleError (L n) (R n) (M n))) atTop (nhds 0))
    (hunion : Tendsto (fun n =>
      halfMeasure.real
        (zrs_sideFamily (zbd_sideHasInfinite (L n)) 0 ∪
          zrs_sideFamily (zbd_sideHasInfinite (L n)) 1 ∪
          zrs_sideFamily (zbd_sideHasInfinite (L n)) 2 ∪
          zrs_sideFamily (zbd_sideHasInfinite (L n)) 3)) atTop (nhds 1))
    (hcross : ∀ n, zbd_twoScaleMerge (L n) (R n) (M n) ⊆ A n ∪ B n) :
    ZhangGeometricData halfMeasure A B := by
  apply zrs_geometricData_of_remaining
    (fun n => zbd_sideHasInfinite (L n))
    (fun n => zbd_twoScaleError (L n) (R n) (M n))
    hbaseInc hbaseM herr hunion
  intro n omega hcap
  have hcap' : omega ∈ zbd_sideHasInfinite (L n) ∩ zbd_sideHasInfinite (R n) := by
    simpa [hopp n] using hcap
  rcases zbd_twoScale_merge_cover (L n) (R n) (M n) hcap' with hmerge | herror
  · exact Or.inl (hcross n hmerge)
  · exact Or.inr herror

end StatMech.TwoDim
