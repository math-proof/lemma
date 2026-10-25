/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangClose.Part2
import Theorem.StatisticalMechanics.Code.TwoDim.SelfDualDichotomy
import Def.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry.Part2
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality


theorem zrs_geometricData_Ssym
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (base : ℕ → Set (ConfigSpace (Sym2 (Site 2))))
    (Err : ℕ → Set (ConfigSpace (Sym2 (Site 2))))
    (hbaseInc : ∀ n, IsIncreasing (base n))
    (hbaseM : ∀ n, MeasurableSet (base n))
    (herr : Tendsto (fun n => halfMeasure.real (Err n)) atTop (𝓝 0))
    (hunion : Tendsto (fun n =>
        halfMeasure.real (zrs_sideFamily (base n) 0 ∪ zrs_sideFamily (base n) 1
          ∪ zrs_sideFamily (base n) 2 ∪ zrs_sideFamily (base n) 3)) atTop (𝓝 1))
    (hmerge : ∀ n, zrs_sideFamily (base n) 0 ∩ zrs_sideFamily (base n) 1
        ⊆ (A n ∪ B n) ∪ Err n) :
    ∀ i n, halfMeasure.real
        ((zrs_geometricData_of_remaining base Err hbaseInc hbaseM herr hunion hmerge).S i n)
      = halfMeasure.real
        ((zrs_geometricData_of_remaining base Err hbaseInc hbaseM herr hunion hmerge).S 0 n) :=
  (zrs_geometricData_of_remaining base Err hbaseInc hbaseM herr hunion hmerge).Ssym


theorem zrs_zhangUnion_of_remaining
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hpa : PositivelyAssociated halfMeasure)
    (base : ℕ → Set (ConfigSpace (Sym2 (Site 2))))
    (Err : ℕ → Set (ConfigSpace (Sym2 (Site 2))))
    (hbaseInc : ∀ n, IsIncreasing (base n))
    (hbaseM : ∀ n, MeasurableSet (base n))
    (herr : Tendsto (fun n => halfMeasure.real (Err n)) atTop (𝓝 0))
    (hunion : Tendsto (fun n =>
        halfMeasure.real (zrs_sideFamily (base n) 0 ∪ zrs_sideFamily (base n) 1
          ∪ zrs_sideFamily (base n) 2 ∪ zrs_sideFamily (base n) 3)) atTop (𝓝 1))
    (hmerge : ∀ n, zrs_sideFamily (base n) 0 ∩ zrs_sideFamily (base n) 1
        ⊆ (A n ∪ B n) ∪ Err n) :
    Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1) :=
  zhg_union_of_geometricData halfMeasure hpa
    (zrs_geometricData_of_remaining base Err hbaseInc hbaseM herr hunion hmerge)

end TwoDim
end StatMech
