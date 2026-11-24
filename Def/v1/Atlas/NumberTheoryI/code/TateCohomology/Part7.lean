module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Def.v1.Atlas.NumberTheoryI.code.Cor2328
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor2328
public import Theorem.v1.Atlas.NumberTheoryI.code.TateCohomology.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

noncomputable def tateH0_equiv_pi_zmod {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ)) ≃ (Fin n → ZMod (Fintype.card G₀)) := by

  refine (Submodule.Quotient.equiv _ _ (invEquivTrivFinFun n)
    (map_normImage_trivFinFun n)).toEquiv |>.trans ?_

  rw [range_smul_id_eq_pi]

  refine (Submodule.quotientPi _).toEquiv |>.trans ?_

  exact Equiv.piCongrRight (fun _ =>
    (Int.quotientSpanEquivZMod _).toEquiv.trans
      (Equiv.cast (by simp [Int.natAbs_natCast])))

end TateCohomology
end
