/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part2


namespace StatMech.Universality

open scoped BigOperators

open Filter Topology


structure HexHalfClass (a : ℂ) (h0 : ℤ) (x : ℝ) (memD memB : List ℤ → Prop) where
  
  lower : {ts // memD ts} → {ts // memB ts}
  
  upper : {ts // memD ts} → {ts // memB ts}
  
  hlow : ∀ d, hexSAWwt a h0 x (lower d).1
    = hexSAWwt a h0 x (d.1.take (hexW2_cutPos h0 d.1))
  

  hupp : ∀ d, hexSAWwt a h0 x (upper d).1
    = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
        (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1))
  

  pair_inj : Function.Injective (fun d => (lower d, upper d))


end StatMech.Universality
