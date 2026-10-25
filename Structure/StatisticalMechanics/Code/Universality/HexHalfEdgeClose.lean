/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


structure HexHalvesInColumn (h0 : ℤ) (memD memB : List ℤ → Prop) where
  
  htake : ∀ d : {ts // memD ts}, memB (d.1.take (hexW2_cutPos h0 d.1))
  
  hdrop : ∀ d : {ts // memD ts}, memB (d.1.drop (hexW2_cutPos h0 d.1))


end StatMech.Universality
