module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Universality.RSWStrip.Part3
public import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
public import Def.StatisticalMechanics.Code.Universality.RSWBxpAssembly
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean -/
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

open StatMech.RSW.Strip


instance rba_selfDualMeasure_isProbabilityMeasure :
    IsProbabilityMeasure rba_selfDualMeasure := by
  unfold rba_selfDualMeasure; infer_instance


end Universality
end StatMech
