/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.CardyDiscreteHolo.Part5


namespace StatMech.Universality

open Complex


noncomputable def cardyObservable (L : CardyLocalConfig) (v d : ℂ) : ℂ → ℂ := fun z =>
  if z = (triFace v d 0 + triFace v d 1) / 2 then L.crossingFun 0
  else if z = (triFace v d 1 + triFace v d 2) / 2 then L.crossingFun 1
  else if z = (triFace v d 2 + triFace v d 0) / 2 then L.crossingFun 2
  else 0


end StatMech.Universality
