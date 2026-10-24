/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.NumberTheoryI.code.DirectLimits
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.DirectLimits

open scoped RestrictedProduct
open Filter Set Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {ι : Type*} [DecidableEq ι]

namespace RestrictedProduct

section XS_Definitions

variable (X : ι → Type*) (U : (i : ι) → Set (X i))

def XS (S : Finset ι) : Set ((i : ι) → X i) :=
  {x | ∀ i, i ∉ S → x i ∈ U i}

theorem XS_mono {S T : Finset ι} (hST : S ⊆ T) : XS X U S ⊆ XS X U T :=
  fun _ hx i hi => hx i (fun hS => hi (hST hS))

def supportFinset (x : Πʳ i, [X i, U i]) : Finset ι :=
  (eventually_cofinite.mp x.2).toFinset

theorem mem_XS_support (x : Πʳ i, [X i, U i]) :
    (x : (i : ι) → X i) ∈ XS X U (supportFinset X U x) := by
  intro i hi
  simp only [supportFinset, Finite.mem_toFinset, mem_setOf_eq, not_not] at hi; exact hi

theorem XS_mem_restricted {S : Finset ι} {x : (i : ι) → X i}
    (hx : x ∈ XS X U S) : ∀ᶠ i in cofinite, x i ∈ U i := by
  rw [eventually_cofinite]
  exact S.finite_toSet.subset (fun i hi => by
    simp only [mem_setOf_eq] at hi
    by_contra h; exact hi (hx i (by simpa using h)))

def inclusionMap {S T : Finset ι} (h : S ⊆ T) :
    XS X U S → XS X U T :=
  fun ⟨x, hx⟩ => ⟨x, XS_mono X U h hx⟩

def transitionMaps :
    ∀ (S T : Finset ι), S ≤ T → XS X U S → XS X U T :=
  fun _ _ h => inclusionMap X U h

abbrev DirectLimitXS :=
  TopologicalSpace.DirectLimit.Space
    (fun S : Finset ι => XS X U S)
    (transitionMaps X U)

open TopologicalSpace.DirectLimit in
def toDirectLimit (x : Πʳ i, [X i, U i]) : DirectLimitXS X U :=
  of (fun S : Finset ι => XS X U S) (transitionMaps X U)
    (supportFinset X U x) ⟨(x : (i : ι) → X i), mem_XS_support X U x⟩

open TopologicalSpace.DirectLimit in
noncomputable def fromDirectLimit : DirectLimitXS X U → Πʳ i, [X i, U i] :=
  lift (fun S : Finset ι => XS X U S) (transitionMaps X U)
    (fun S (x : ↥(XS X U S)) => ⟨x.val, XS_mem_restricted X U x.prop⟩)
    (fun S T h x => by simp only [transitionMaps, inclusionMap])

def toChunk (S : Finset ι) (x : ↥(XS X U S)) :
    Πʳ i, [X i, U i]_[Filter.principal ((↑S : Set ι)ᶜ)] :=
  RestrictedProduct.mk x.val (by
    rw [Filter.eventually_principal]
    intro i hi
    exact x.prop i (by simpa using hi))
