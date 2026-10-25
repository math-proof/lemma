/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk


namespace StatMech.Universality

open HexWalk

noncomputable def hexEndpointSAWFinset (a : ℂ) (h0 : ℤ) : ℕ → Finset (List ℤ)
  | 0 => {[]}
  | n + 1 =>
      (hlc_sawFinset a h0 n).image (fun ts => ts ++ [(1 : ℤ)]) ∪
      (hlc_sawFinset a h0 n).image (fun ts => ts ++ [(-1 : ℤ)])


noncomputable def hexEndpointSAWCount (a : ℂ) (h0 : ℤ) (n : ℕ) : ℕ :=
  (hexEndpointSAWFinset a h0 n).card


end StatMech.Universality
