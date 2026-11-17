/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Def.StatisticalMechanics.Code.Onsager.ChordCut.Part3


public section

namespace StatMech.Onsager.ChordCut

open scoped BigOperators


structure BoxData where
  
  B : Finset Pt
  
  x1 : ℤ
  
  hx1 : ∀ p ∈ B, p.1 ≤ x1


end StatMech.Onsager.ChordCut
