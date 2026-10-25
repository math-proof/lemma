/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Theorem.v1.Atlas.AlgebraicGeometryI.code.IsFiniteTypeOfCoversTop
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.IsFiniteTypeOfCoversTop
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PushforwardPreservesKernel
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSpecFinitelyGenerated
import Def.v1.Atlas.AlgebraicGeometryI.code.PushforwardPreservesKernel
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSpecFinitelyGenerated
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Prop19PushforwardEmbedding
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheaves


namespace CoherentSheaves

open CategoryTheory Limits AlgebraicGeometry in
/-- A sheaf of modules `F` on a scheme `X` is *coherent* if it is quasi-coherent and of
finite type. -/
class IsCoherentSheaf {X : Scheme.{u}} (F : X.Modules) : Prop where
  isQC : (F : SheafOfModules.{u} X.ringCatSheaf).IsQuasicoherent
  isFT : (F : SheafOfModules.{u} X.ringCatSheaf).IsFiniteType

end CoherentSheaves
