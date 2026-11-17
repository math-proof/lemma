/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.CardyDiscreteHolo.Part2


public section

namespace StatMech.Universality

open Complex


structure CardyLocalConfig where
  
  Ω : Type
  
  [fin : Fintype Ω]
  
  rot : Ω → Ω
  
  rot_bij : Function.Bijective rot
  
  arc : Ω → ZMod 3
  
  arc_rot : ∀ ω, arc (rot ω) = arc ω + 1
  
  weight : Ω → ℂ
  
  weight_rot : ∀ ω, weight (rot ω) = weight ω

end StatMech.Universality
