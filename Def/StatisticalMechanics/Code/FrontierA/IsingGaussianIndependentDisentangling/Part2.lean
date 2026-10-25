/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIntersectionUnionBound.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedEq22Refinement
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeFirstComponentSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j : V) (S : Finset V)
    (pq : IndependentPairProfiles G) : Real :=
  ((if sources G (ofEdgeFun G pq.1) = {i, j}
      then weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = ∅
      then weight G beta J (ofEdgeFun G pq.2) else 0)) *
    (if notConnComp G
        (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) i = S then 1 else 0)

noncomputable def finiteTreeConfinementSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (k l : V) (S : Finset V)
    (pq : IndependentPairProfiles G) : Real :=
  ((if sources G (ofEdgeFun G pq.1) = {k, l}
      then weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = ∅
      then weight G beta J (ofEdgeFun G pq.2) else 0)) *
    (if k ∈ finiteTreeSafeRegion G
        (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) Sᶜ then 1 else 0)

noncomputable def finiteTreeIndependentDisjointSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (z : IndependentFourProfiles G) : Real :=
    ((if sources G (ofEdgeFun G z.1.1) = {i, j}
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = ∅
        then weight G beta J (ofEdgeFun G z.1.2) else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = {k, l}
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0)) *
    (if ¬ ∃ y : V,
        CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) i y ∧
        CurrentConnected G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k y
      then 1 else 0)


noncomputable def finiteTreeIndependentDisjointFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑' z : IndependentFourProfiles G,
    finiteTreeIndependentDisjointSummand G beta J i j k l z

end StatMech.FrontierA
