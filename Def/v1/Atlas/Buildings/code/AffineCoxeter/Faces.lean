/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/Faces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.Buildings.code.AffineCoxeter.AffineCriterion.Part2
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace AffineCoxeterFaces

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The affine reflection hyperplane $H_{s} \cap E$ obtained by intersecting the Coxeter wall
$H_s = \{x : x_s = 0\}$ with the affine hyperplane $E = \{x : \langle v_0, x\rangle = 1\}$. -/
def affineReflectionHyperplane (M : CoxeterMatrix B) (v₀ : B → ℝ) (s : B) :
    Set (B → ℝ) :=
  coxeterWall M s ∩ affineHyperplane M v₀

/-- The arrangement of affine reflection hyperplanes in $E$: one hyperplane $\{y : \langle\alpha, y\rangle = 0\} \cap E$
for each positive root $\alpha \in \Phi^+$. -/
def affineHyperplaneSystem (M : CoxeterMatrix B) [inst : RootSystemData M]
    (v₀ : B → ℝ) : Set (Set (B → ℝ)) :=
  {η | ∃ α ∈ inst.Φpos, η = {y : B → ℝ | pairing α y = 0} ∩ affineHyperplane M v₀}

/-- The **affine face** of type $I \subseteq B$: intersection of the Tits face $F_I$ with the
affine hyperplane $E$. -/
def affineFace (M : CoxeterMatrix B) (v₀ : B → ℝ) (I : Finset B) :
    Set (B → ℝ) :=
  titsFaceDual M I ∩ affineHyperplane M v₀

/-- The **affine fundamental chamber** $C \cap E$: the strict fundamental chamber for $W$ acting
on $E$. -/
def affineFundamentalChamber (M : CoxeterMatrix B) (v₀ : B → ℝ) :
    Set (B → ℝ) :=
  titsFundamentalChamber M ∩ affineHyperplane M v₀

/-- Points in the open affine fundamental chamber $C \cap E$ lie strictly off every reflecting
hyperplane: $\langle \alpha, x \rangle \ne 0$ for all $\alpha \in \Phi^+$. -/
def vertexMapToE (M : CoxeterMatrix B) (v₀ : B → ℝ)
    (s₀ : B) : Set (B → ℝ) :=
  titsFaceDual M ({s₀}ᶜ) ∩ affineHyperplane M v₀

/-- Every point of $E$ lies on a **unique** affine face $F_I \cap E$: the affine faces partition $E$,
realizing the geometric Coxeter complex as a stratification of the affine hyperplane. -/
def affineFaceLE (M : CoxeterMatrix B) (v₀ : B → ℝ)
    (I J : Finset B) : Prop :=
  affineFace M v₀ J ⊆ closure (affineFace M v₀ I)

end AffineCoxeterFaces
