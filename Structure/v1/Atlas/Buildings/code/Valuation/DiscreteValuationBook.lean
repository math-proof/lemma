/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DiscreteValuationBook.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
open Polynomial


section TopologicalGroup

/-- *Proposition-valued version of `IsTopologicalGroup`*: a group $G$ with a topology such
that multiplication and inversion are continuous. Used as a `Prop` (rather than a structure)
so it can be carried through hypotheses without instance issues. -/
structure TopologicalGroupProp (G : Type*) [TopologicalSpace G] [Group G] : Prop where
  mul_continuous : Continuous (fun p : G × G => p.1 * p.2)
  inv_continuous : Continuous (Inv.inv : G → G)

end TopologicalGroup
