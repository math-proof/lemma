/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflection
open Filter Metric Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

@[simp] theorem mem_reflectComplexSet {S : Set Complex} {z : Complex} :
    z ∈ reflectComplexSet S ↔ (starRingEnd Complex) z ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨(starRingEnd Complex) z, hz, by simp⟩

theorem reflectComplexSet_isOpen {S : Set Complex} (hS : IsOpen S) :
    IsOpen (reflectComplexSet S) := by
  simpa [reflectComplexSet, Complex.conjCLE_apply] using
    Complex.conjCLE.toHomeomorph.isOpenMap S hS

theorem reflectComplexSet_isPreconnected {S : Set Complex}
    (hS : IsPreconnected S) : IsPreconnected (reflectComplexSet S) := by
  exact hS.image (starRingEnd Complex) Complex.continuous_conj.continuousOn

theorem reflectComplexSet_isCompact {S : Set Complex} (hS : IsCompact S) :
    IsCompact (reflectComplexSet S) :=
  hS.image Complex.continuous_conj

@[simp] theorem reflectComplexSet_reflectComplexSet (S : Set Complex) :
    reflectComplexSet (reflectComplexSet S) = S := by
  ext z
  simp


theorem tendstoLocallyUniformlyOn_reflect_iff
    {ι : Type*} {p : Filter ι} {F : ι → Complex → Complex}
    {f : Complex → Complex} {S : Set Complex} :
    TendstoLocallyUniformlyOn
        (fun n z ↦ F n ((starRingEnd Complex) z))
        (fun z ↦ f ((starRingEnd Complex) z)) p (reflectComplexSet S) ↔
      TendstoLocallyUniformlyOn F f p S := by
  constructor
  · intro h
    have hcomp := h.comp (starRingEnd Complex)
      (fun _ hz ↦ mem_reflectComplexSet.mpr (by simpa using hz))
      Complex.continuous_conj.continuousOn
    simpa [Function.comp_def] using hcomp
  · intro h
    have hcomp := h.comp (starRingEnd Complex)
      (fun _ hz ↦ mem_reflectComplexSet.mp hz)
      Complex.continuous_conj.continuousOn
    simpa [Function.comp_def] using hcomp

theorem closure_reflectComplexSet (S : Set Complex) :
    closure (reflectComplexSet S) = reflectComplexSet (closure S) := by
  simpa [reflectComplexSet, Complex.conjCLE_apply] using
    (Complex.conjCLE.toHomeomorph.image_closure S).symm


end
end StatMech.Universality
