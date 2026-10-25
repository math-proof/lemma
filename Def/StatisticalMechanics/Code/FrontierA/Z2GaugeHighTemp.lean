/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.StatisticalMechanics.Code.FrontierA.Z2GaugeHighTemp
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

section GaugeHypergraph

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

def gaugeEdgeSpin (omega : GaugeConfig E) (e : E) : ℝ :=
  if omega e then 1 else -1


def plaquetteSpin (incidence : P -> Finset E) (omega : GaugeConfig E) (p : P) : ℝ :=
  ∏ e ∈ incidence p, gaugeEdgeSpin omega e


def plaquetteIncidenceCount (incidence : P -> Finset E) (A : Finset P) (e : E) : Nat :=
  ∑ p ∈ A, if e ∈ incidence p then 1 else 0


def IsClosedPlaquetteSet (incidence : P -> Finset E) (A : Finset P) : Prop :=
  ∀ e, Even (plaquetteIncidenceCount incidence A e)


def HasWilsonBoundary (incidence : P -> Finset E) (A : Finset P)
    (L : Finset E) : Prop :=
  ∀ e, Even (plaquetteIncidenceCount incidence A e + if e ∈ L then 1 else 0)


def wilsonSpin (L : Finset E) (omega : GaugeConfig E) : ℝ :=
  ∏ e ∈ L, gaugeEdgeSpin omega e


def gaugeAction (incidence : P -> Finset E) (K : P -> ℝ)
    (omega : GaugeConfig E) : ℝ :=
  ∑ p, K p * plaquetteSpin incidence omega p


noncomputable def gaugeWeight (incidence : P -> Finset E) (K : P -> ℝ)
    (omega : GaugeConfig E) : ℝ :=
  Real.exp (gaugeAction incidence K omega)


noncomputable def gaugePartition (incidence : P -> Finset E) (K : P -> ℝ) : ℝ :=
  ∑ omega : GaugeConfig E, gaugeWeight incidence K omega


noncomputable def gaugeWilsonNumerator (incidence : P -> Finset E) (K : P -> ℝ)
    (L : Finset E) : ℝ :=
  ∑ omega : GaugeConfig E, wilsonSpin L omega * gaugeWeight incidence K omega

end GaugeHypergraph
end StatMech.FrontierA
