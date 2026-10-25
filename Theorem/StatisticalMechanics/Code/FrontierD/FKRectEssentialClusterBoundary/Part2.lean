/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialClusterBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClusterBoundary.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Def.StatisticalMechanics.Code.FrontierD.FKRectEssentialClusterBoundary.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectClusterBoundaryPerm_val
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (d : {d : FKMedialDart R.medialTorus //
      d ∈ fkRectClusterBoundaryDarts R omega x}) :
    (fkRectClusterBoundaryPerm R omega x d).1 =
      fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega) d.1 :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ d)


theorem fkRectClusterBoundaryDarts_iterate_mem
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    {d : FKMedialDart R.medialTorus}
    (hd : d ∈ fkRectClusterBoundaryDarts R omega x) :
    ∀ n : Nat,
      (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R omega))^[n] d ∈
          fkRectClusterBoundaryDarts R omega x := by
  intro n
  induction n with
  | zero => simpa using hd
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact fkRectClusterBoundaryDarts_boundaryStep_mem R omega x ih


theorem fkRectWindingIndependent_comm (u v : Int × Int) :
    FKRectWindingIndependent u v ↔ FKRectWindingIndependent v u := by
  unfold FKRectWindingIndependent
  constructor <;> intro h <;> intro hzero <;> apply h
  · nlinarith
  · nlinarith


theorem fkRect_boundaryOrbit_winding_dependent_of_not_hasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (x : R.Vertex) (q : (fkRectOpenGraph R omega).Walk x x)
    (hold : ¬ FKRectHasNet R omega)
    (d : FKMedialDart R.medialTorus)
    (hxd : (fkRectOpenGraph R omega).Reachable x
      (fkRectMedialDartPrimalLabel R d)) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
      (fkRectWalkWinding R q) := by
  intro hind
  apply hold
  exact FKRectHasNet.of_connected_closedWalks R omega hxd q
    (fkRectMedialBoundaryPrimalOrbitWalk R omega d)
    ((fkRectWindingIndependent_comm _ _).mp hind)

end
end StatMech.FrontierD
