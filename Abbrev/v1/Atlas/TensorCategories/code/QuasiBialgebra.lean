/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Def.v1.Atlas.TensorCategories.code.QuasiBialgebra.Part4
@[expose] public section

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


/-- Reference abbreviation for Definition 1.34.5: a quasi-bialgebra. -/
abbrev Definition_1_34_5_QuasiBialgebra := @QuasiBialgebra

/-- Reference abbreviation for Definition 1.34.6: a twist for a quasi-bialgebra. -/
abbrev Definition_1_34_6 := @QuasiBialgebraTwist

/-- Reference abbreviation for Definition 1.34.6: the twist data. -/
abbrev Definition_1_34_6_Twist := @QuasiBialgebraTwist

/-- Reference abbreviation for Definition 1.34.6: twist equivalence of quasi-bialgebras. -/
abbrev Definition_1_34_6_TwistEquiv := @QuasiBialgebraTwistEquiv

/-- Reference abbreviation for Definition 1.35.2: an antipode on a quasi-bialgebra. -/
abbrev Definition_1_35_2_Antipode := @QuasiBialgebraAntipode

/-- Reference abbreviation for Definition 1.35.2: a quasi-Hopf algebra. -/
abbrev Definition_1_35_2_QuasiHopfAlgebra := @QuasiHopfAlgebra

