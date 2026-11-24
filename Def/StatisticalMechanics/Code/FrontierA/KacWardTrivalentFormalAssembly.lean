module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFormalMultiaffine
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardTrivalentCoefficients
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalCoefficient.Part3
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager

universe u


noncomputable def kwGraphFormalEvenPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    MvPowerSeries (Sym2 V) ℂ :=
  ∑ F ∈ evenSubgraphs G,
    MvPowerSeries.monomial (ons_finsetExponent F) 1


noncomputable def kwGraphEvenMvPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    MvPolynomial (Sym2 V) ℂ :=
  ∑ F ∈ evenSubgraphs G,
    MvPolynomial.monomial (ons_finsetExponent F) 1

end StatMech.FrontierA
