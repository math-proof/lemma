/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BernsteinGelfandEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.HCBimoduleProjectives.Part2
import Lemma.Fin.All_Eq.of.All_Eq.All_Eq_RightAction.All_Eq_RightAction.All_Any_Eq_Sum_RightAction
import Lemma.Int.IsInQPlus0
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.Level1.ne.Top
import Lemma.Int.FGUeaIotaRange
import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Def.v1.Atlas.LieGroups.code.JantzenFiltration.Part2
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Analysis.Complex.Basic
import Instance.v1.Atlas.LieGroups.code.BernsteinGelfandEquivalence


noncomputable section

open TensorProduct

universe u_R u_g u_mod

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]

variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

@[reducible] def LieBimodule.instLieRingModuleOfLeftAction
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) : LieRingModule g Y.carrier where
  bracket x m := Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m
  add_lie x y m := by
    show Y.leftAction (UniversalEnvelopingAlgebra.ι R (x + y)) m =
      Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m +
      Y.leftAction (UniversalEnvelopingAlgebra.ι R y) m
    rw [map_add, map_add, LinearMap.add_apply]
  lie_add x m n := by
    show Y.leftAction (UniversalEnvelopingAlgebra.ι R x) (m + n) =
      Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m +
      Y.leftAction (UniversalEnvelopingAlgebra.ι R x) n
    rw [map_add]
  leibniz_lie x y m := by
    show Y.leftAction (UniversalEnvelopingAlgebra.ι R x)
        (Y.leftAction (UniversalEnvelopingAlgebra.ι R y) m) =
      Y.leftAction (UniversalEnvelopingAlgebra.ι R ⁅x, y⁆) m +
      Y.leftAction (UniversalEnvelopingAlgebra.ι R y)
        (Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m)
    rw [LieHom.map_lie, Ring.lie_def, map_sub, LinearMap.sub_apply, map_mul, map_mul]
    show Y.leftAction _ (Y.leftAction _ m) =
      Y.leftAction _ (Y.leftAction _ m) - Y.leftAction _ (Y.leftAction _ m) +
      Y.leftAction _ (Y.leftAction _ m)
    abel

@[reducible] def LieBimodule.instLieModuleOfLeftAction
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) :
    @LieModule R g Y.carrier _ _ _ Y.instAddCommGroup Y.instModule
      Y.instLieRingModuleOfLeftAction :=
  @LieModule.mk R g Y.carrier _ _ _ Y.instAddCommGroup Y.instModule
    Y.instLieRingModuleOfLeftAction
    (fun r x m => by
      change Y.leftAction (UniversalEnvelopingAlgebra.ι R (r • x)) m =
        r • Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m
      rw [map_smul, map_smul, LinearMap.smul_apply])
    (fun r x m => by
      change Y.leftAction (UniversalEnvelopingAlgebra.ι R x) (r • m) =
        r • Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m
      rw [map_smul])

end
