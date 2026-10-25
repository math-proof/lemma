/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part6
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusSpinGlue_add_field_eq_embeds
    (i : Fin d) (h : IsingDyadicTorus d k → Real)
    (lower upper : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusSpinField (isingTorusGlueHalves i lower upper) + h =
      isingTorusEmbedLower i (isingTorusLowerValues i h lower) +
        isingTorusEmbedUpper i (isingTorusUpperValues i h upper) := by
  funext x
  by_cases hx : isingTorusInLowerHalf i x
  · have hs : isingTorusGlueHalves i lower upper x = lower ⟨x, hx⟩ := by
      simp [isingTorusGlueHalves, hx]
    have hspin : spin (isingTorusGlueHalves i lower upper) x =
        spin lower ⟨x, hx⟩ := by
      unfold spin
      rw [hs]
    change spin (isingTorusGlueHalves i lower upper) x + h x = _
    rw [hspin]
    simp [isingTorusEmbedLower, isingTorusEmbedUpper,
      isingTorusLowerValues, hx]
  · have hs : isingTorusGlueHalves i lower upper x =
        upper ⟨isingTorusReflectSite i x,
          (isingTorusReflectSite_not_lower_iff i x).mpr hx⟩ := by
      simp [isingTorusGlueHalves, hx]
    have hspin : spin (isingTorusGlueHalves i lower upper) x =
        spin upper ⟨isingTorusReflectSite i x,
          (isingTorusReflectSite_not_lower_iff i x).mpr hx⟩ := by
      unfold spin
      rw [hs]
    change spin (isingTorusGlueHalves i lower upper) x + h x = _
    rw [hspin]
    simp [isingTorusEmbedLower, isingTorusEmbedUpper,
      isingTorusUpperValues, hx]

end StatMech.FrontierA
