/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalStructuresGraded.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalFunctorsCohomology
set_option maxHeartbeats 400000

universe u v


section PartI

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

/-- The pullback of a 3-cochain `ω` along a group automorphism `φ`. -/
def autPullback3 (φ : G ≃* G) (ω : Cochain3' G A) : Cochain3' G A :=
  fun g h l => ω (φ g) (φ h) (φ l)

/-- Two 3-cochains are in the same automorphism orbit if some automorphism of `G` maps the
class of one to the class of the other in `H³(G, A)`. -/
def AutOrbitCohomologous3 (ω₁ ω₂ : Cochain3' G A) : Prop :=
  ∃ (φ : G ≃* G), Cohomologous3 G A ω₁ (autPullback3 G A φ ω₂)

end PartI
