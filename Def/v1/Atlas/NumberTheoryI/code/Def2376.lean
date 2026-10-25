/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Def2376.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.Thm2375
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Limits.Preserves.Finite
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
