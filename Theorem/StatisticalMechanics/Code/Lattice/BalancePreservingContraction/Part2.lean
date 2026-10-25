/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnetEar
import Def.StatisticalMechanics.Code.Lattice.BalancePreservingContraction
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem bpc_dartNext_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (h : bpc_NotProbed c e) :
    dartNext (K \ {c}) e = dartNext K e := by
  apply bpc_dartNext_agree
  · constructor
    · intro hh; exact (Set.mem_diff _).mp hh |>.1
    · intro hh; refine (Set.mem_diff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.1
  · constructor
    · intro hh; exact (Set.mem_diff _).mp hh |>.1
    · intro hh; refine (Set.mem_diff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.2


theorem bpc_turnZ_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (h : bpc_NotProbed c e) : turnZ (K \ {c}) e = turnZ K e := by
  apply bpc_turnZ_agree
  · constructor
    · intro hh; exact (Set.mem_diff _).mp hh |>.1
    · intro hh; refine (Set.mem_diff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.1
  · constructor
    · intro hh; exact (Set.mem_diff _).mp hh |>.1
    · intro hh; refine (Set.mem_diff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.2


theorem bpc_iterate_dartNext_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] e)) (k : ℕ) :
    (dartNext (K \ {c}))^[k] e = (dartNext K)^[k] e := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact bpc_dartNext_diff_singleton K c ((dartNext K)^[n] e) (hnp n)


theorem bpc_isBoundaryDart_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (he : IsBoundaryDart K e) (hc : c ≠ e.tail) : IsBoundaryDart (K \ {c}) e := by
  refine ⟨⟨he.1, ?_⟩, ?_⟩
  · simp only [Set.mem_singleton_iff]; exact fun h => hc h.symm
  · intro hh; exact he.2 hh.1


theorem bpc_isPeriodicPt_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) (n : ℕ) :
    Function.IsPeriodicPt (dartNextSub (K \ {c})) n a' ↔
      Function.IsPeriodicPt (dartNextSub K) n a := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  have key : (dartNext (K \ {c}))^[n] a'.1 = (dartNext K)^[n] a.1 := by
    rw [hval]; exact bpc_iterate_dartNext_diff_singleton K c a.1 hnp n
  constructor
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    rw [key, hval] at hv
    change ((dartNextSub K)^[n] a).1 = a.1
    rw [dartNextSub_iterate_val]; exact hv
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    change ((dartNextSub (K \ {c}))^[n] a').1 = a'.1
    rw [dartNextSub_iterate_val, key, hval]; exact hv


theorem bpc_dartOrbitPeriod_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
    dartOrbitPeriod (K \ {c}) a' = dartOrbitPeriod K a := by
  unfold dartOrbitPeriod
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  exact bpc_isPeriodicPt_diff_singleton K c a a' hval hnp n


theorem bpc_cornerBalance_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
    cornerBalance (K \ {c}) a' = cornerBalance K a := by
  classical
  unfold cornerBalance
  rw [bpc_dartOrbitPeriod_diff_singleton K c a a' hval hnp]
  set p := dartOrbitPeriod K a with hp
  have hright : rightCornerCount (K \ {c}) a'.1 p = rightCornerCount K a.1 p := by
    unfold rightCornerCount
    congr 2
    apply Finset.filter_congr
    intro i _
    rw [hval, bpc_iterate_dartNext_diff_singleton K c a.1 hnp i,
        bpc_turnZ_diff_singleton K c ((dartNext K)^[i] a.1) (hnp i)]
  have hleft : leftCornerCount (K \ {c}) a'.1 p = leftCornerCount K a.1 p := by
    unfold leftCornerCount
    congr 2
    apply Finset.filter_congr
    intro i _
    rw [hval, bpc_iterate_dartNext_diff_singleton K c a.1 hnp i,
        bpc_turnZ_diff_singleton K c ((dartNext K)^[i] a.1) (hnp i)]
  rw [hright, hleft]


end Lattice
end StatMech
