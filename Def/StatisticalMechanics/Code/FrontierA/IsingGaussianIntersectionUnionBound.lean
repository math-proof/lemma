/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIntersectionUnionBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourCurrentTree
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingGaussianIntersectionUnionBound
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def finiteTreeSeparatedFourSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l y : V)
    (z : TreeFourProfiles G) : Real :=
  ((if sources G (ofEdgeFun G z.1.1) = grahamPairSupport i j
      then weight G beta J (ofEdgeFun G z.1.1) else 0) *
    (if sources G (ofEdgeFun G z.1.2) = ∅
      then weight G beta J (ofEdgeFun G z.1.2) else 0) *
    (if CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y
      then 1 else 0)) *
  ((if sources G (ofEdgeFun G z.2.1) = grahamPairSupport k l
      then weight G beta J (ofEdgeFun G z.2.1) else 0) *
    (if sources G (ofEdgeFun G z.2.2) = ∅
      then weight G beta J (ofEdgeFun G z.2.2) else 0) *
    (if CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
      then 1 else 0))


noncomputable def finiteTreeIndependentIntersectionSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (z : TreeFourProfiles G) : Real :=
  ((if sources G (ofEdgeFun G z.1.1) = grahamPairSupport i j
      then weight G beta J (ofEdgeFun G z.1.1) else 0) *
    (if sources G (ofEdgeFun G z.1.2) = ∅
      then weight G beta J (ofEdgeFun G z.1.2) else 0)) *
  ((if sources G (ofEdgeFun G z.2.1) = grahamPairSupport k l
      then weight G beta J (ofEdgeFun G z.2.1) else 0) *
    (if sources G (ofEdgeFun G z.2.2) = ∅
      then weight G beta J (ofEdgeFun G z.2.2) else 0)) *
  (if ∃ y : V,
      CurrentConnected G
        (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
      CurrentConnected G
        (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
    then 1 else 0)


noncomputable def finiteTreeIndependentIntersectionFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑' z : TreeFourProfiles G,
    finiteTreeIndependentIntersectionSummand G beta J i j k l z

end StatMech.FrontierA
