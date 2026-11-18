module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Artinian.Module
set_option maxHeartbeats 800000

public section

open Coalgebra HopfAlgebra WithConv LinearMap
open scoped TensorProduct

universe u v


section AntipodeSq

section Def_1_22_13

variable {R : Type u} {A : Type v}

example [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
    (g : A) (hg : IsGroupLikeElem R g) :
    Coalgebra.comul g = g ⊗ₜ[R] g :=
  hg.comul_eq_tmul_self

example [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A] :
    Type v := GroupLike R A

example [CommSemiring R] [Nontrivial R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
    (g : A) (hg : IsGroupLikeElem R g) : g ≠ 0 :=
  hg.ne_zero

end Def_1_22_13
end AntipodeSq
