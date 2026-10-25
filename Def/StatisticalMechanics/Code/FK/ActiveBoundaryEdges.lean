/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
open scoped BigOperators
open Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


noncomputable def activeBCWeight (pf : Sym2 V -> Real) (q : Real)
    (omega : ConfigSpace G.edgeSet) : Real :=
  edgeProductW G pf (extendActive G omega) *
    q ^ numClustersBC G C (extendActive G omega)

noncomputable def activeBCZ (pf : Sym2 V -> Real) (q : Real) : Real :=
  ∑ omega : ConfigSpace G.edgeSet, activeBCWeight G C pf q omega

noncomputable def activeBCProb (pf : Sym2 V -> Real) (q : Real)
    (omega : ConfigSpace G.edgeSet) : Real :=
  activeBCWeight G C pf q omega / activeBCZ G C pf q

noncomputable def activeBCMean (pf : Sym2 V -> Real) (q : Real)
    (f : ConfigSpace G.edgeSet -> Real) : Real :=
  ∑ omega, f omega * activeBCProb G C pf q omega

noncomputable def activeBCCov (pf : Sym2 V -> Real) (q : Real)
    (f g : ConfigSpace G.edgeSet -> Real) : Real :=
  activeBCMean G C pf q (fun omega => f omega * g omega) -
    activeBCMean G C pf q f * activeBCMean G C pf q g

noncomputable def activeBCNumer (pf : Sym2 V -> Real) (q : Real)
    (f : ConfigSpace G.edgeSet -> Real) : Real :=
  ∑ omega, f omega * activeBCWeight G C pf q omega

noncomputable def activeBCProbOf (pf : Sym2 V -> Real) (q : Real)
    (A : Set (ConfigSpace G.edgeSet)) : Real :=
  activeBCMean G C pf q (A.indicator fun _ => (1 : Real))

end FK
end StatMech
