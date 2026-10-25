/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Algebra.Homology.AlternatingConst
import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section5.Part2
open CategoryTheory

universe u₀


namespace HomotopyInvariance

open CategoryTheory HomologicalComplex

universe v u

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable {f₀ f₁ : C ⟶ D}

/-- **Lemma 5.10**. Chain-homotopic chain maps induce the same map on homology:
if `f₀, f₁ : C → D` are chain homotopic, then `H_n(f₀) = H_n(f₁)`. -/
theorem chainHomotopy_homologyMap_eq (h : ChainHomotopy f₀ f₁) (i : ι)
    [C.HasHomology i] [D.HasHomology i] :
    homologyMap f₀ i = homologyMap f₁ i :=
  Homotopy.homologyMap_eq h i

end HomotopyInvariance
