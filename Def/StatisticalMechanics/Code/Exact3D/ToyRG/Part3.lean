/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ToyRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Abbrev.StatisticalMechanics.Code.Exact3D.ToyRG.Part2

@[expose] public section

namespace StatMech

namespace Exact3D

noncomputable def toyHyperbolicRGMap (scale : BlockScale)
    (thermalEigenvalue stableEigenvalue : ℝ) :
    BlockSpinMap toyHyperbolicHamiltonianSpace where
  scale := scale
  map := fun x => (thermalEigenvalue * x.1, stableEigenvalue * x.2)


end Exact3D
end StatMech
