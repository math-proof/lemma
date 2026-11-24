module
public import Theorem.StatisticalMechanics.Code.TwoDim.ZhangClose.Part2
public import Theorem.StatisticalMechanics.Code.TwoDim.SelfDualDichotomy
public import Theorem.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality


def zrs_rot (A : Set (ConfigSpace (Sym2 (Site 2)))) : Set (ConfigSpace (Sym2 (Site 2))) :=
  kdi_rotConfig ⁻¹' A


def zrs_sideFamily (base : Set (ConfigSpace (Sym2 (Site 2)))) :
    Fin 4 → Set (ConfigSpace (Sym2 (Site 2))) :=
  ![base, zrs_rot (zrs_rot base), zrs_rot base, zrs_rot (zrs_rot (zrs_rot base))]

end TwoDim
end StatMech
