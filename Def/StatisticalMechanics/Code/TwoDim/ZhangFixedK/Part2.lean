/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


noncomputable def zfk_translateOpenIso (t : Site 2)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraph 2 (translateConfig t omega) ≃g openSubgraph 2 omega where
  toEquiv := Equiv.addRight t
  map_rel_iff' := fun {x y} => (cti_isOpenEdge_translate t omega x y).symm

end StatMech.TwoDim
