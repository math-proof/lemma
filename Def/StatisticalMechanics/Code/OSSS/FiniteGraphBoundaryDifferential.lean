/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FiniteGraphBoundaryDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ActiveBoundaryDifferential
import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
open scoped BigOperators Classical
open Finset Set


namespace StatMech.OSSS.FiniteGraphBoundaryDifferential

open RevealmentConstruction LindebergTree DecisionTree

open FrontierFamilyClose FamilyEqzzzResolution

open ActiveEdgeDifferential ActiveBoundaryDifferential

open PrefixCoversClose ReachBoxCrossing

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {E : Type*} [Fintype E] [DecidableEq E]

def openCrossEvent (endU endV : E → V) (o : V) (B : Set V) :
    Set (ConfigSpace E) :=
  {omega | ConnOpenSet endU endV omega o B}

noncomputable def openIncidentEdges
    (endU endV : E → V) (o : V) : Finset E :=
  Finset.univ.filter (fun e => endU e = o ∨ endV e = o)

noncomputable def reindexedOpenIncidentEdges
    {I O : Type*} [Fintype I] [DecidableEq I] [DecidableEq O]
    (iota : I → O) (endU endV : I → V) (o : V) : Finset O :=
  (openIncidentEdges endU endV o).image iota

end StatMech.OSSS.FiniteGraphBoundaryDifferential
