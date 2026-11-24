module
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Theorem.Set.Closure.eq.N.of.Eq
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Invariant.Basic
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
public import Def.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

set_option maxHeartbeats 800000 in
open FractionalIdeal in
lemma normOnFracUnits_kills_principal (K L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    (toPrincipalIdeal (𝓞 L) (FractionRing (𝓞 L))).range ≤
    (normOnFracUnits K L).ker := by
  intro I hI
  rw [MonoidHom.mem_ker]
  have hI1 : ClassGroup.mk (FractionRing (𝓞 L)) I = 1 := by
    rw [ClassGroup.mk_eq_one_iff]
    obtain ⟨x, hx⟩ := hI
    rw [← hx, coe_toPrincipalIdeal]
    exact ⟨x, coe_spanSingleton _ _⟩
  show normToClK K L ⟨ClassGroup.integralRep (I : _), _⟩ = 1
  exact normToClK_of_mk0_eq_one (by rw [ClassGroup.mk0_integralRep, hI1])

end ArtinUnramified
end
