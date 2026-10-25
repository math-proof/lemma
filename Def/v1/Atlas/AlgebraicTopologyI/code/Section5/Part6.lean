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
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section5.Part3
open CategoryTheory

universe u₀


namespace HomotopyTheory

open CategoryTheory AlgebraicTopology HomologicalComplex Limits

/-- The continuous self-map of `X` constant at the point `b ∈ X`. -/
def topConstAt {X : TopCat.{0}} (b : X) : X ⟶ X :=
  ⟨fun _ => b, continuous_const⟩

/-- The unique continuous projection `X → *` to the one-point space. -/
def topProjToPoint (X : TopCat.{0}) : X ⟶ TopCat.of PUnit :=
  ⟨fun _ => PUnit.unit, continuous_const⟩

/-- The continuous inclusion `* → X` of the one-point space picking out `b ∈ X`. -/
def topInclFromPoint {X : TopCat.{0}} (b : X) : TopCat.of PUnit ⟶ X :=
  ⟨fun _ => b, continuous_const⟩

/-- A homotopy equivalence of topological spaces `X ≃ Y` lifts to a chain homotopy
equivalence of singular chain complexes. This is the chain-level form of Corollary 5.5,
combining Theorem 5.2 / Proposition 5.11 with the definition of homotopy equivalence. -/
noncomputable def singularChainHomotopyEquivOfHomotopyEquiv
    {C : Type*} [Category C] [HasCoproducts.{0} C] [Preadditive C]
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (R : C) :
    _root_.HomotopyEquiv
      (((singularChainComplexFunctor C).obj R).obj (TopCat.of X))
      (((singularChainComplexFunctor C).obj R).obj (TopCat.of Y)) := by
  let F := ((singularChainComplexFunctor C).obj R)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have H_left : TopCat.Homotopy (f ≫ g) (CategoryStruct.id (TopCat.of X)) :=
    Classical.choice e.left_inv
  have H_right : TopCat.Homotopy (g ≫ f) (CategoryStruct.id (TopCat.of Y)) :=
    Classical.choice e.right_inv
  exact
    { hom := F.map f
      inv := F.map g
      homotopyHomInvId :=
        (_root_.Homotopy.ofEq (F.map_comp f g).symm).trans
          ((H_left.singularChainComplexFunctorObjMap R).trans
            (_root_.Homotopy.ofEq (F.map_id (TopCat.of X))))
      homotopyInvHomId :=
        (_root_.Homotopy.ofEq (F.map_comp g f).symm).trans
          ((H_right.singularChainComplexFunctorObjMap R).trans
            (_root_.Homotopy.ofEq (F.map_id (TopCat.of Y)))) }

/-- **Proposition 5.13**. For a nonempty star-shaped subset `s` of a real topological
vector space, the singular chain complex `S_*(s; ℤ)` is chain-homotopy equivalent to the
chain complex `ℤ` concentrated in degree zero. Combines contractibility of `s` with the
chain-level homotopy invariance and identification of `S_*(*)` with `ℤ`. -/
noncomputable def starShaped_singularHomology
    {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    {s : Set E} {b : E} (hstar : StarConvex ℝ b s) (hne : s.Nonempty) :
    _root_.HomotopyEquiv
      (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of ↥s))
      ((ChainComplex.single₀ AddCommGrpCat).obj (AddCommGrpCat.of ℤ)) := by
  letI : ContractibleSpace ↥s := hstar.contractibleSpace hne

  let e := Classical.choice (ContractibleSpace.hequiv_unit ↥s)
  let step1 := singularChainHomotopyEquivOfHomotopyEquiv e (AddCommGrpCat.of ℤ)

  let iso1 := singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
    AddCommGrpCat (AddCommGrpCat.of ℤ) (TopCat.of Unit)

  let step3 := ChainComplex.alternatingConstHomotopyEquiv
    (∐ fun _ : (TopCat.of Unit) ↦ (AddCommGrpCat.of ℤ))

  let iso2 := (ChainComplex.single₀ AddCommGrpCat).mapIso
    (coproductUniqueIso (fun _ : (TopCat.of Unit) ↦ (AddCommGrpCat.of ℤ)))
  exact step1.trans ((HomotopyEquiv.ofIso iso1).trans (step3.trans (HomotopyEquiv.ofIso iso2)))

end HomotopyTheory

namespace HomotopyInvariance

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe v' u' w'

/-- **Proposition 5.11**. A homotopy `H : f₀ ≃ f₁` between continuous maps `X → Y`
determines a natural chain homotopy between the induced chain maps
`f₀*, f₁* : S_*(X) → S_*(Y)`. -/
noncomputable def singularChainHomotopy_of_homotopy
    {C : Type u'} [Category.{v'} C] [Preadditive C] [HasCoproducts.{w'} C]
    {X Y : TopCat.{w'}} {f₀ f₁ : X ⟶ Y}
    (H : TopCat.Homotopy f₀ f₁) (R : C) :
    Homotopy (((singularChainComplexFunctor C).obj R).map f₀)
      (((singularChainComplexFunctor C).obj R).map f₁) :=
  H.singularChainComplexFunctorObjMap R

end HomotopyInvariance
