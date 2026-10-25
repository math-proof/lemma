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
open scoped BigOperators Classical
open Finset Set Filter Topology


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPeriodic

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open WiredBoxDifferential FK RevealmentTranslation

open FKSharpnessWeighted

open ActiveBoundaryDifferential ActiveEdgeDifferential LindebergTree


def translateAmbientEdge {d : Nat} (x : Site d) (e : Sym2 (Site d)) :
    Sym2 (Site d) :=
  Sym2.map (fun y => y + x) e


def PhaseCovariant {d : Nat} {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real) : Prop :=
  forall x e, J (translateAmbientEdge x e) = phaseJ (phase x) e


def boxCoupling {d : Nat} (J : Sym2 (Site d) -> Real) (R : Nat) :
    Sym2 (boxVerts d R) -> Real :=
  fun e => J (Sym2.map Subtype.val e)


def transBoxCoupling {d : Nat} (J : Sym2 (Site d) -> Real)
    (R : Nat) (x : Site d) : Sym2 (fvs_transBoxVerts d R x) -> Real :=
  fun e => J (Sym2.map Subtype.val e)


def phaseBoxCoupling {d : Nat} {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P) (R : Nat) :
    Sym2 (boxVerts d R) -> Real :=
  boxCoupling (phaseJ a) R


end FKSharpnessWeightedPeriodic
end OSSS
end StatMech
