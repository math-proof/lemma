/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
public import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
public import Theorem.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
public import Theorem.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
public import Theorem.Finset.IsMaximalToSimplicialComplex.of.IsMaximal.In_Apartments
public import Def.v1.Atlas.Buildings.code.Building.Labels
public import Def.v1.Atlas.Buildings.code.Building.RetractionDef
public import Structure.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
public import Structure.v1.Atlas.Buildings.code.BNPair.FromBuilding.Part2

@[expose] public section

set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


namespace BNPairFromBuildingData

variable {V : Type*} [DecidableEq V]
  {G : Type*} [Group G]
  {b : Building V}
  {ct : Building.CoxeterTypeOfBuilding b}
  (data : BNPairFromBuildingData G b ct)

/-- The **Borel subgroup** $B$: the stabilizer of the base chamber $C_0$. -/
def B : Subgroup G := data.act.chamberStabilizer data.C₀

/-- The **subgroup $N$**: the stabilizer of the base apartment $A_0$. -/
def N : Subgroup G := data.act.apartmentStabilizer data.A₀

/-- The **torus** $T$: stabilizer of both $C_0$ and $A_0$, i.e. $T = B \cap N$. -/
def T : Subgroup G := data.act.torus data.C₀ data.A₀

/-- The underlying function of the projection $\pi : N \to W$: send $n \in N$ to
$\varphi(n \cdot C_0)$, i.e. the chamber of $A_0$ that $n$ maps $C_0$ to, read off as a
Weyl group element via $\varphi$. -/
def πFun (n : data.N) : ct.matrix.Group :=
  data.φ (data.act.smulFace (n : G) data.C₀)

/-- The Weyl projection $\pi : N \to W$ as a group homomorphism, packaging `πFun` with its
multiplicativity and unit-preservation. -/
def π : data.N →* ct.matrix.Group where
  toFun := data.πFun
  map_one' := by
    simp only [πFun]
    rw [show ((1 : data.N) : G) = (1 : G) from rfl]
    rw [data.act.smulFace_one]
    exact data.φ_base
  map_mul' := data.πFun_mul

end BNPairFromBuildingData
