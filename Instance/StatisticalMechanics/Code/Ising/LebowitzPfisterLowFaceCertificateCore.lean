/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceCertificateCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificateCore

@[expose] public section

open Finset


namespace StatMech.Ising

namespace LowFaceCertificate

instance : OfNat TriPoly n where ofNat := .const n

instance : Add TriPoly := ⟨TriPoly.add⟩

instance : Neg TriPoly := ⟨TriPoly.neg⟩

instance : Sub TriPoly := ⟨fun p q => p.add q.neg⟩

instance : Mul TriPoly := ⟨TriPoly.mul⟩

instance : Pow TriPoly Nat := ⟨TriPoly.pow⟩

end LowFaceCertificate
end StatMech.Ising
