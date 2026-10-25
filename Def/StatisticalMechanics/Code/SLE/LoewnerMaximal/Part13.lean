/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part13
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

noncomputable def loewnerMaximalMapsHomeomorph
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    loewnerUnswallowedDomain W t ≃ₜ upperHalfPlane where
  toFun := MapsTo.restrict (loewnerMaximalMaps W t)
    (loewnerUnswallowedDomain W t) upperHalfPlane
    (loewnerMaximalMaps_bijOn_upperHalfPlane hW ht).1
  invFun := MapsTo.restrict (loewnerMaximalMapsInverse hW ht)
    upperHalfPlane (loewnerUnswallowedDomain W t)
    (fun _ hy ↦ loewnerMaximalMapsInverse_mem hW ht hy)
  left_inv := by
    intro x
    apply Subtype.ext
    exact (eq_loewnerMaximalMapsInverse_of_mapsTo hW ht x.2
      (loewnerMaximalMaps_mem_upperHalfPlane x.2) rfl).symm
  right_inv := by
    intro y
    apply Subtype.ext
    exact loewnerMaximalMaps_inverse hW ht y.2
  continuous_toFun :=
    (continuousOn_loewnerMaximalMaps hW ht).mapsToRestrict
      (loewnerMaximalMaps_bijOn_upperHalfPlane hW ht).1
  continuous_invFun :=
    (continuousOn_loewnerMaximalMapsInverse hW ht).mapsToRestrict
      (fun _ hy ↦ loewnerMaximalMapsInverse_mem hW ht hy)


end StatMech.SLE
