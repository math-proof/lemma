/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.Tactic.Group
import Instance.v1.Atlas.TensorCategories.code.GradedVec.Part3
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section Rigidity

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- Dual object of `X = ⟨g⟩` in `CG G A ω`, namely `⟨g⁻¹⟩`. -/
def CG.dualObj (X : CG G A ω) : CG G A ω := ⟨X.val⁻¹⟩

/-- The evaluation morphism `Xᘁ ⊗ X ⟶ 𝟙` in `CG G A ω`, given by the scalar
`ω(g, g⁻¹, g)⁻¹` where `g = X.val`. -/
def CG.evalMorphism (X : CG G A ω) :
    CG.tensorObj' (CG.dualObj X) X ⟶ CG.unit' where
  val := (ω.toFun X.val X.val⁻¹ X.val)⁻¹
  eq := by simp [CG.dualObj]

/-- The coevaluation morphism `𝟙 ⟶ X ⊗ Xᘁ` in `CG G A ω`, given by the
scalar `1`. -/
def CG.coevMorphism (X : CG G A ω) :
    CG.unit' ⟶ CG.tensorObj' X (CG.dualObj X) where
  val := 1
  eq := by simp [CG.dualObj]

end Rigidity
