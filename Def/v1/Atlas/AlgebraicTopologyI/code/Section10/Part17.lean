/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section10
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace SphereHomology

open AlgebraicTopology

open AlgebraicTopology

/-- **Off-degree vanishing of sphere homology.** For `n > 0`, `0 < q ≠ n`, we have
`H_q(S^n) = 0`. The proof is a two-variable induction on `q + n`, combining
`sphere_h1_vanishing`, `sphere_zero_homology_vanishing`, and `suspension_vanishing_step`. -/
noncomputable def homotopyEquiv_singularHomologyIso {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (q : ℕ) :
    SingularHomologyGroup q X ≅ SingularHomologyGroup q Y := by
  open AlgebraicTopology CategoryTheory in

  let F := ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ))
  let fwd : (TopCat.of X) ⟶ (TopCat.of Y) := TopCat.ofHom e.toFun
  let bwd : (TopCat.of Y) ⟶ (TopCat.of X) := TopCat.ofHom e.invFun


  let Hl := e.left_inv.some
  let Hr := e.right_inv.some
  change F.obj (TopCat.of X) ≅ F.obj (TopCat.of Y)

  have hfwd_bwd : F.map (fwd ≫ bwd) = F.map (𝟙 _) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (show TopCat.Homotopy (fwd ≫ bwd) (𝟙 _) from Hl)
      (AddCommGrpCat.of ℤ) q
  have hbwd_fwd : F.map (bwd ≫ fwd) = F.map (𝟙 _) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (show TopCat.Homotopy (bwd ≫ fwd) (𝟙 _) from Hr)
      (AddCommGrpCat.of ℤ) q
  have h1 : F.map fwd ≫ F.map bwd = 𝟙 _ := by
    rw [← F.map_comp, hfwd_bwd, F.map_id]
  have h2 : F.map bwd ≫ F.map fwd = 𝟙 _ := by
    rw [← F.map_comp, hbwd_fwd, F.map_id]
  exact ⟨F.map fwd, F.map bwd, h1, h2⟩

/-- A homeomorphism `f : X ≃ₜ Y` restricts to a homeomorphism
`{x | x ≠ p} ≃ₜ {y | y ≠ f p}` between punctured spaces. -/
def homeomorphSubtypeNe {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (x : X) :
    {y : X | y ≠ x} ≃ₜ {z : Y | z ≠ f x} where
  toEquiv := f.toEquiv.subtypeEquiv fun _ =>
    ⟨fun h => f.injective.ne h, fun h e => h (congrArg f e)⟩
  continuous_toFun :=
    Continuous.subtype_mk ((map_continuous f).comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk ((map_continuous f.symm).comp continuous_subtype_val) _

/-- Translation by `-p` gives a homeomorphism `{x | x ≠ p} ≃ₜ {y | y ≠ 0}`. -/
def puncturedTranslateHomeomorph {G : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] (p : G) :
    {x : G | x ≠ p} ≃ₜ {y : G | y ≠ 0} := by
  refine (homeomorphSubtypeNe (Homeomorph.addRight (-p)) p).trans
    (Homeomorph.ofEqSubtypes ?_)
  ext x
  simp [add_neg_cancel]

end SphereHomology
