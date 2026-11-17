/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_52_6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Class.v1.Atlas.TensorCategories.code.Definition_1_52_6
@[expose] public section

open CategoryTheory MonoidalCategory

universe u v

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [RigidCategory C] [HasDistinguishedInvertibleData C]


/-- Definition 1.52.6 (unimodular category): a finite tensor category whose
distinguished invertible object is isomorphic to the unit. -/
abbrev Definition_1_52_6 : Prop := IsUnimodularCategory' C

/-- Alias for `Definition_1_52_6`; expresses unimodularity of `C`. -/
abbrev def_1_52_6 : Prop := IsUnimodularCategory' C

