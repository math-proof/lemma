/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Def2376.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.NumberTheoryI.code.Thm2375
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

@[expose] public section

open CategoryTheory Category MonoidalCategory

universe u

set_option maxHeartbeats 800000


noncomputable def TorGroup
    (R : Type u) [CommRing R] (n : ℕ) (M A : ModuleCat.{u} R) :
    ModuleCat.{u} R :=
  ((Tor' (ModuleCat.{u} R) n).obj M).obj A

noncomputable def TorGroup.functor
    (R : Type u) [CommRing R] (n : ℕ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  Tor' (ModuleCat.{u} R) n

section TorDeltaFunctorAuxiliary

noncomputable def torRes (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    ProjectiveResolution M := ProjectiveResolution.of M

end TorDeltaFunctorAuxiliary
