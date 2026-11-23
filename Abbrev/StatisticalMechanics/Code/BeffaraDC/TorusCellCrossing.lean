/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Onsager.Torus
public import Inductive.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing
@[expose] public section

open SimpleGraph


namespace StatMech.BeffaraDC

open StatMech.Onsager


abbrev TorusEdgeCode (L : ℕ) :=
  (ZMod L × ZMod L) × TorusEdgeOrientation


abbrev TorusAmbientEdge (L : ℕ) [Fact (2 < L)] :=
  {e : Sym2 (ZMod L × ZMod L) // e ∈ (onsTorusGraph L).edgeFinset}


end StatMech.BeffaraDC
