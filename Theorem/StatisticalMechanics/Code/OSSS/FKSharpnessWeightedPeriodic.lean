/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeighted
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxLocalized.Part3
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxOffCentre.Part4
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic
open scoped BigOperators Classical
open Finset Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPeriodic

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open WiredBoxDifferential FK RevealmentTranslation

open FKSharpnessWeighted

open ActiveBoundaryDifferential ActiveEdgeDifferential LindebergTree


theorem transBoxCoupling_map_eq_phaseBoxCoupling
    {d : Nat} {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hcov : PhaseCovariant J phase phaseJ)
    (R : Nat) (x : Site d) (e : Sym2 (boxVerts d R)) :
    transBoxCoupling J R x (Sym2.map (fvs_transEquiv d R x) e) =
      phaseBoxCoupling phaseJ (phase x) R e := by
  unfold transBoxCoupling phaseBoxCoupling boxCoupling
  rw [Sym2.map_map]
  have hfun :
      (Subtype.val ∘ (fvs_transEquiv d R x : boxVerts d R ->
        fvs_transBoxVerts d R x)) = (fun y : boxVerts d R => (y : Site d) + x) := by
    funext y
    rfl
  rw [hfun]
  calc
    J (Sym2.map (fun y : boxVerts d R => (y : Site d) + x) e) =
        J (translateAmbientEdge x (Sym2.map Subtype.val e)) := by
      congr 1
      unfold translateAmbientEdge
      rw [Sym2.map_map]
      rfl
    _ = phaseJ (phase x) (Sym2.map Subtype.val e) :=
      hcov x (Sym2.map Subtype.val e)

theorem PhaseCovariant.eq_of_same_phase
    {d : Nat} {P : Type*}
    {J : Sym2 (Site d) -> Real} {phase : Site d -> P}
    {phaseJ : P -> Sym2 (Site d) -> Real}
    (hcov : PhaseCovariant J phase phaseJ)
    {x y : Site d} (hxy : phase x = phase y) (e : Sym2 (Site d)) :
    J (translateAmbientEdge x e) = J (translateAmbientEdge y e) := by
  rw [hcov x e, hcov y e, hxy]

theorem PhaseCovariant.phaseCoupling_pos
    {d : Nat} {P : Type*}
    {J : Sym2 (Site d) -> Real} {phase : Site d -> P}
    {phaseJ : P -> Sym2 (Site d) -> Real}
    (hcov : PhaseCovariant J phase phaseJ)
    (hsurj : Function.Surjective phase) (hJ : forall e, 0 < J e) :
    forall a e, 0 < phaseJ a e := by
  intro a e
  obtain ⟨x, rfl⟩ := hsurj a
  rw [← hcov x e]
  exact hJ _


theorem betaParams_transBox_map_eq_phaseBox
    {d : Nat} {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hcov : PhaseCovariant J phase phaseJ)
    (R : Nat) (x : Site d) (beta : Real) (e : Sym2 (boxVerts d R)) :
    FK.betaParams (transBoxCoupling J R x) beta
        (Sym2.map (fvs_transEquiv d R x) e) =
      FK.betaParams (phaseBoxCoupling phaseJ (phase x) R) beta e := by
  unfold FK.betaParams
  rw [transBoxCoupling_map_eq_phaseBoxCoupling J phase phaseJ hcov R x e]


end FKSharpnessWeightedPeriodic
end OSSS
end StatMech
