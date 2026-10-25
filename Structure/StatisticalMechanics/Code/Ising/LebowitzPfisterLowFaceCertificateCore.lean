/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceCertificateCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.List.FinRange
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic
open Finset


namespace StatMech.Ising

namespace LowFaceCertificate

structure TriTerm where
  ex : Nat
  ey : Nat
  ez : Nat
  coeff : Int
  deriving DecidableEq

structure TriPoly where
  terms : List TriTerm

end LowFaceCertificate
end StatMech.Ising
