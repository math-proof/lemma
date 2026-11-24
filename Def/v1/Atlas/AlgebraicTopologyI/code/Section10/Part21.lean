module
public import Mathlib
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section10.Part9
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BrouwerFixedPoint

open Metric Set Inner

variable {X : Type u} [TopologicalSpace X]

/-- The homotopy equivalence relation on self-maps of `S`: two continuous maps `f, g : S → S`
are related iff there is a homotopy from `f` to `g`. -/
def selfMapSetoid (S : TopCat.{0}) : Setoid (S ⟶ S) where
  r f g := Nonempty (TopCat.Homotopy f g)
  iseqv := {
    refl := fun _ => ⟨ContinuousMap.Homotopy.refl _⟩
    symm := fun ⟨H⟩ => ⟨H.symm⟩
    trans := fun ⟨H₁⟩ ⟨H₂⟩ => ⟨H₁.trans H₂⟩
  }

/-- Homotopy classes of self-maps of `S`, denoted `[S, S]`. -/
def SelfMapHomotopyClass (S : TopCat.{0}) := Quotient (selfMapSetoid S)

end BrouwerFixedPoint
