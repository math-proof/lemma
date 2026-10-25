/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part6


namespace StatMech.Universality

open Complex


noncomputable def isingObservable (D : IsingMedialVertex) (v d : ℂ) : ℂ → ℂ := fun z =>
  if z = (isingFace v d 0 + isingFace v d 1) / 2 then D.edgeObs 0
  else if z = (isingFace v d 1 + isingFace v d 2) / 2 then D.edgeObs 3
  else if z = (isingFace v d 2 + isingFace v d 3) / 2 then D.edgeObs 1
  else if z = (isingFace v d 3 + isingFace v d 0) / 2 then D.edgeObs 2
  else 0


end StatMech.Universality
