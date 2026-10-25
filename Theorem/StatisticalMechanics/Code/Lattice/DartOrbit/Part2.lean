/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Def.StatisticalMechanics.Code.Lattice.DartOrbit
open SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem dartNextSub_val (K : Set (Site 2)) (e : {e : Dart // IsBoundaryDart K e}) :
    (dartNextSub K e).1 = dartNext K e.1 := rfl


theorem dartNextSub_injective (K : Set (Site 2)) :
    Function.Injective (dartNextSub K) := by
  intro a b h
  exact Subtype.ext (dartNext_injOn K a.2 b.2 (congrArg Subtype.val h))


theorem dartNextSub_iterate_val (K : Set (Site 2)) (e : {e : Dart // IsBoundaryDart K e})
    (k : ℕ) : ((dartNextSub K)^[k] e).1 = (dartNext K)^[k] e.1 := by
  induction k generalizing e with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl


theorem dartNextSub_ne_self (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    dartNextSub K a ≠ a := by
  intro h
  exact dartNext_ne_self K a.1 a.2 (congrArg Subtype.val h)


theorem dartNext_periodic (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    ∃ p > 0, (dartNext K)^[p] e = e := by
  have hfin : Finite {e : Dart // IsBoundaryDart K e} := (boundaryDarts_finite K hK).to_subtype
  have hmem := (dartNextSub_injective K).mem_periodicPts ⟨e, he⟩
  rw [Function.mem_periodicPts] at hmem
  obtain ⟨p, hp, hper⟩ := hmem
  refine ⟨p, hp, ?_⟩
  have := congrArg Subtype.val hper
  rwa [dartNextSub_iterate_val] at this


end Lattice
end StatMech
