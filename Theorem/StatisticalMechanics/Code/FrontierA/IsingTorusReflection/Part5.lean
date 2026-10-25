/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part4
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusPolarizeLower_reflection_invariant
    (i : Fin d) (h : IsingDyadicTorus d k → Real) (x : IsingDyadicTorus d k) :
    isingTorusPolarizeLower i h (isingTorusReflectSite i x) =
      isingTorusPolarizeLower i h x := by
  unfold isingTorusPolarizeLower
  by_cases hx : isingTorusInLowerHalf i x
  · have hr : ¬ isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      fun hr => (isingTorusReflectSite_not_lower_iff i x).mp hr hx
    simp [hx, hr]
  · have hr : isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      (isingTorusReflectSite_not_lower_iff i x).mpr hx
    simp [hx, hr]

theorem isingTorusPolarizeUpper_reflection_invariant
    (i : Fin d) (h : IsingDyadicTorus d k → Real) (x : IsingDyadicTorus d k) :
    isingTorusPolarizeUpper i h (isingTorusReflectSite i x) =
      isingTorusPolarizeUpper i h x := by
  unfold isingTorusPolarizeUpper
  by_cases hx : isingTorusInLowerHalf i x
  · have hr : ¬ isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      fun hr => (isingTorusReflectSite_not_lower_iff i x).mp hr hx
    simp [hx, hr]
  · have hr : isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      (isingTorusReflectSite_not_lower_iff i x).mpr hx
    simp [hx, hr]


end StatMech.FrontierA
