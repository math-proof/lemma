/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Module.Prod
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section11.Part3

@[expose] public section

open Set Topology

universe u


namespace EilenbergSteenrod

attribute [instance] TopPair.instTop

/-- Two maps of pairs are homotopic if there exists a homotopy of pair maps between them. -/
def AreHomotopic {P Q : TopPair} (f₀ f₁ : MapOfPairs P Q) : Prop :=
  Nonempty (HomotopyOfPairMaps f₀ f₁)

end EilenbergSteenrod
