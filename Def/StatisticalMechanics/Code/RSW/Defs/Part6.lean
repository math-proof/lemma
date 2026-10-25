/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part5
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


def IsAnnulusCircuit (ω : ConfigSpace (Sym2 (Site 2))) (z : Site 2) (n : ℕ)
    {v : Site 2} (w : (openSubgraph 2 ω).Walk v v) : Prop :=
  IsOpenCircuit 2 ω w ∧ ∀ u ∈ w.support, u ∈ annulus z n


def AnnulusCircuit (ω : ConfigSpace (Sym2 (Site 2))) (z : Site 2) (n : ℕ) : Prop :=
  ∃ (v : Site 2) (w : (openSubgraph 2 ω).Walk v v), IsAnnulusCircuit ω z n w


def annulusCircuitEvent (z : Site 2) (n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | AnnulusCircuit ω z n}

end Box
end RSW
end StatMech
