module
public import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenBoxGeneral.Part3
open Set SimpleGraph Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}

noncomputable local instance bgfdPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p


end StatMech.FrontierA
