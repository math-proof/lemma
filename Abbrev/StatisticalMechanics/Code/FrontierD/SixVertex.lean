/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Hom.PowersetCard
public import Structure.StatisticalMechanics.Code.FrontierD.SixVertex
@[expose] public section

open Finset Matrix


namespace StatMech.FrontierD

abbrev EvenTorus.Vertex (T : EvenTorus) := Fin T.width × Fin T.height


end StatMech.FrontierD
