module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
public import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
public import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
public import Theorem.StatisticalMechanics.Code.Universality.KestenHalf
public import Theorem.StatisticalMechanics.Code.TwoDim.SelfDualDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.RSWProbDualityClose
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box


noncomputable def rpd_reindexInv :
    ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) crossEdge.symm


end Universality
end StatMech
