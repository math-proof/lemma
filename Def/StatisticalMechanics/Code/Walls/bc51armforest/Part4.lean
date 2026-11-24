module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
public import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
public import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bc50arminjection.Part2
public import Instance.StatisticalMechanics.Code.Walls.bc51armforest
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
set_option linter.style.longLine false
set_option maxRecDepth 4000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


namespace Bc51Witness

def catG : SimpleGraph (Fin 6) := SimpleGraph.fromRel catE

end Bc51Witness
end StatMech.Walls
