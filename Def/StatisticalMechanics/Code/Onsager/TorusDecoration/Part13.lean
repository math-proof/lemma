/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part12


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

noncomputable def ons_decoratedPortEquiv (L : ℕ) [Fact (2 < L)] :
    {D : Finset (Sym2 (ons_Dart L)) //
      D ∈ evenSubgraphs (ons_decGraph L)} ≃ ons_PortPattern L where
  toFun D := ons_portPatternOfDecorated L D.1 D.2
  invFun P := ⟨ons_decoratedEdges P, ons_decoratedEdges_even L P⟩
  left_inv D := Subtype.ext (ons_decoratedEdges_portPatternOfDecorated L D.1 D.2)
  right_inv P := ons_portPatternOfDecorated_decoratedEdges L P


noncomputable def ons_decorationEquiv (L : ℕ) [Fact (2 < L)] :
    {F : Finset (Sym2 (ZMod L × ZMod L)) //
      F ∈ evenSubgraphs (onsTorusGraph L)} ≃
    {D : Finset (Sym2 (ons_Dart L)) //
      D ∈ evenSubgraphs (ons_decGraph L)} :=
  (ons_evenSubgraphPortEquiv L).trans (ons_decoratedPortEquiv L).symm


end StatMech.Onsager
