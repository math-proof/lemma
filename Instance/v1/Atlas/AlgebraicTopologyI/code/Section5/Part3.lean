module
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
public import Mathlib.Algebra.Homology.AlternatingConst
public import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part3
open CategoryTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u₀


namespace HomotopyCategory

namespace HoTop

/-- Categorical data on `HoTop`: morphisms `X ⟶ Y` are homotopy classes of continuous
maps, identities are the classes of `id`, and composition is induced from composition
of representatives (well-defined because homotopy is compatible with composition). -/
instance : CategoryStruct HoTop.{u₀} where
  Hom X Y := Quotient (homotopicSetoid X Y)
  id X := ⟦ContinuousMap.id X⟧
  comp := Quotient.map₂ (fun f g => g.comp f)
    (fun _ _ hf _ _ hg => hg.comp hf)

/-- `HoTop` is a category: composition is associative and the homotopy classes of
identities act as left and right units. -/
instance : Category HoTop.{u₀} where
  id_comp f := by
    induction f using Quotient.ind
    exact congr_arg (⟦·⟧) (ContinuousMap.id_comp _)
  comp_id f := by
    induction f using Quotient.ind
    exact congr_arg (⟦·⟧) (ContinuousMap.comp_id _)
  assoc f g h := by
    induction f using Quotient.ind
    induction g using Quotient.ind
    induction h using Quotient.ind
    exact congr_arg (⟦·⟧) (ContinuousMap.comp_assoc _ _ _)

end HoTop
end HomotopyCategory
