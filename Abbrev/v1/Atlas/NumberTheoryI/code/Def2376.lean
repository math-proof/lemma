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
import Def.v1.Atlas.NumberTheoryI.code.Def2376
open CategoryTheory Category MonoidalCategory

universe u

set_option maxHeartbeats 800000


section TorDeltaFunctorAuxiliary

noncomputable abbrev tR (R : Type u) [CommRing R] :=
  tensoringRight (ModuleCat.{u} R)

end TorDeltaFunctorAuxiliary
