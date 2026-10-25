/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Def.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem SameOrbit.refl (K : Set (Site 2)) (e : Dart) : SameOrbit K e e := ⟨0, rfl⟩


theorem SameOrbit.trans {K : Set (Site 2)} {e f g : Dart}
    (h1 : SameOrbit K e f) (h2 : SameOrbit K f g) : SameOrbit K e g := by
  obtain ⟨m, hm⟩ := h1
  obtain ⟨n, hn⟩ := h2
  refine ⟨n + m, ?_⟩
  rw [Function.iterate_add_apply, hm, hn]


theorem SameOrbit.symm_of_finite {K : Set (Site 2)} (hK : K.Finite) {e f : Dart}
    (he : IsBoundaryDart K e) (h : SameOrbit K e f) : SameOrbit K f e := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨p, hp, hper⟩ := dartNext_periodic K hK e he
  
  refine ⟨(n / p + 1) * p - n, ?_⟩
  have hle : n ≤ (n / p + 1) * p := by
    have h1 : n / p * p ≤ n := Nat.div_mul_le_self n p
    have h2 : n < n / p * p + p := Nat.lt_div_mul_add hp
    rw [Nat.add_one_mul]
    omega
  rw [← hn, ← Function.iterate_add_apply]
  rw [Nat.sub_add_cancel hle]
  
  have hmul : ∀ k : ℕ, (dartNext K)^[k * p] e = e := by
    intro k
    induction k with
    | zero => simp
    | succ j ih => rw [Nat.succ_mul, Function.iterate_add_apply, hper, ih]
  exact hmul (n / p + 1)


theorem sameComponent_of_sameOrbit (K : Set (Site 2)) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f) (h : SameOrbit K e f) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
  obtain ⟨n, hn⟩ := h
  exact dartNext_orbit_head_sameComponent K e f he hf hn


theorem interfaceConnected_iff_sameOrbit (K : Set (Site 2)) :
    InterfaceConnected K ↔
      ∀ (e f : Dart) (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f),
        ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ →
          SameOrbit K e f :=
  Iff.rfl


end Lattice
end StatMech
