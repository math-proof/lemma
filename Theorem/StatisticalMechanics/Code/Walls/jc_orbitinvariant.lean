/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_orbitinvariant.lean -/

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
open SimpleGraph Function


namespace StatMech.Walls

open StatMech.Lattice


theorem jc_sum_range_cyclic_shift (g : ℕ → ℤ) (p : ℕ) (hcyc : g p = g 0) :
    ∑ i ∈ Finset.range p, g (i + 1) = ∑ i ∈ Finset.range p, g i := by
  have h1 : ∑ i ∈ Finset.range (p + 1), g i = (∑ i ∈ Finset.range p, g (i + 1)) + g 0 :=
    Finset.sum_range_succ' g p
  have h2 : ∑ i ∈ Finset.range (p + 1), g i = (∑ i ∈ Finset.range p, g i) + g p :=
    Finset.sum_range_succ g p
  rw [hcyc] at h2
  omega


theorem jc_dartOrbitPeriod_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    dartOrbitPeriod K (dartNextSub K a) = dartOrbitPeriod K a := by
  have hfin : Finite {e : Dart // IsBoundaryDart K e} := (boundaryDarts_finite K hK).to_subtype
  unfold dartOrbitPeriod
  exact Function.minimalPeriod_apply ((dartNextSub_injective K).mem_periodicPts a)


theorem jc_dartOrbitPeriod_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    dartOrbitPeriod K ((dartNextSub K)^[n] a) = dartOrbitPeriod K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', jc_dartOrbitPeriod_dartNextSub K hK, ih]


theorem jc_totalTurnZ_period_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K (dartNextSub K a).1 (dartOrbitPeriod K (dartNextSub K a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  rw [jc_dartOrbitPeriod_dartNextSub K hK a]
  set p := dartOrbitPeriod K a with hp
  set g := fun i => turnZ K ((dartNext K)^[i] a.1) with hg
  have hper : (dartNext K)^[p] a.1 = a.1 := orbit_iterate_period_eq K a
  have hcyc : g p = g 0 := by simp only [hg, hper, Function.iterate_zero_apply]
  unfold totalTurnZ
  rw [dartNextSub_val]
  have key : ∀ i, (dartNext K)^[i] (dartNext K a.1) = (dartNext K)^[i + 1] a.1 := by
    intro i; rw [Function.iterate_succ_apply]
  simp_rw [key]
  exact jc_sum_range_cyclic_shift g p hcyc


theorem jc_totalTurnZ_period_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    totalTurnZ K ((dartNextSub K)^[n] a).1 (dartOrbitPeriod K ((dartNextSub K)^[n] a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', jc_totalTurnZ_period_dartNextSub K hK, ih]


theorem jc_cornerBalance_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance K (dartNextSub K a) = cornerBalance K a := by
  rw [cornerBalance_eq_totalTurnZ, cornerBalance_eq_totalTurnZ]
  exact jc_totalTurnZ_period_dartNextSub K hK a


theorem jc_cornerBalance_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    cornerBalance K ((dartNextSub K)^[n] a) = cornerBalance K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', jc_cornerBalance_dartNextSub K hK, ih]


theorem jc_cornerBalance_constant_on_orbit (K : Set (Site 2)) (hK : K.Finite)
    (a b : {e : Dart // IsBoundaryDart K e}) (n : ℕ) (hb : b = (dartNextSub K)^[n] a) :
    cornerBalance K b = cornerBalance K a := by
  rw [hb]; exact jc_cornerBalance_iterate_dartNextSub K hK a n


end StatMech.Walls
