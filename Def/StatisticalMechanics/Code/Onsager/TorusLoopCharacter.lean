module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.TorusContractibleLoop


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopCharacter.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_intParity (m : ℤ) : Fin 2 :=
  if Even m then 0 else 1

noncomputable def ons_windingParity (mx my : ℤ) : Fin 2 × Fin 2 :=
  (ons_intParity mx, ons_intParity my)

end StatMech.Onsager
