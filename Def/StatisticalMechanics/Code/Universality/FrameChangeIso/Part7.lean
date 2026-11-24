module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
public import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
public import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
public import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
public import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part7
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


noncomputable def fci_faceDualConfig (w : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) := fun e => !(w (fci_faceEdgeEquiv e))


end Universality
end StatMech
