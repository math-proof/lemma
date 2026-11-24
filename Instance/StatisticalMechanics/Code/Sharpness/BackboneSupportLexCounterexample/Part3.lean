module
public import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
public import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part4
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Sharpness

instance (A : Finset shbK4Edge) : Decidable (shbK4SelectsDirect03 A) := by
  unfold shbK4SelectsDirect03
  infer_instance


end StatMech.Sharpness
