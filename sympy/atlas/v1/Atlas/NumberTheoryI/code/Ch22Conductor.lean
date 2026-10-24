/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22Conductor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.NumberTheoryI.code.LocalFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.LocalFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalCFT
import sympy.atlas.v1.Atlas.NumberTheoryI.code.RayClassFields
import sympy.atlas.v1.Atlas.NumberTheoryI.code.GlobalCFT
noncomputable section

open scoped NumberField
open RayClassField
open Classical in
attribute [local instance] Classical.dec Classical.decPred Classical.decRel Classical.decEq

namespace LocalConductor

def IsArchimedeanLocalField (K : Type*) [IsLocalField K] : Prop :=
  ¬ IsUltrametricDist K

def IsNonarchimedeanLocalField (K : Type*) [IsLocalField K] : Prop :=
  IsUltrametricDist K

def archLocalConductor (K L : Type*) [IsLocalField K] [IsLocalField L]
    [Algebra K L] [FiniteDimensional K L] (_hK : IsArchimedeanLocalField K) : ℕ :=
  if Module.finrank K L = 1 then 0 else 1

def higherUnitGroupSet (K : Type*) [IsLocalField K]
    (_hK : IsNonarchimedeanLocalField K) (n : ℕ) : Set K :=
  if n = 0 then {x : K | ‖x‖ = 1}
  else {x : K | ‖x‖ = 1 ∧ ∀ (π : K), (‖π‖ < 1 ∧ 0 < ‖π‖ ∧
    ∀ (y : K), ‖y‖ < 1 → ‖y‖ ≤ ‖π‖) → ‖x - 1‖ ≤ ‖π‖ ^ n}

def HigherUnitsInNormGroup (K L : Type*) [IsLocalField K] [IsLocalField L]
    [Algebra K L] [FiniteDimensional K L] (hK : IsNonarchimedeanLocalField K) (n : ℕ) : Prop :=
  higherUnitGroupSet K hK n ⊆ Set.range (Algebra.norm K : L → K)

noncomputable def localNormImage (K : Type u) (L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Set (𝔭.adicCompletion K) :=
  ⋃ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw : w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal),
    Set.range (HeightOneSpectrum.localNormHom w 𝔭 (hw ▸ le_refl _))

def FinitePlaceHigherUnitsInNormGroup (K : Type u) (L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : ℕ → Prop :=
  fun n =>
    let K_v := 𝔭.adicCompletion K

    have hK_v : LocalConductor.IsNonarchimedeanLocalField K_v :=
      (inferInstance : IsUltrametricDist K_v)
    LocalConductor.higherUnitGroupSet K_v hK_v n ⊆ localNormImage K L 𝔭

def localConductorAtInfinitePlace (K : Type u) (L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : NumberField.InfinitePlace K) : ℕ :=
  if NumberField.InfinitePlace.IsUnramifiedIn L v then 0 else 1
