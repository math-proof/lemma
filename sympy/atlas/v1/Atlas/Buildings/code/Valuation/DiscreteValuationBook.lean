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

/-- *One Newton iteration*: given $f \in R[X]$ and a current approximation $x$ at which
$f'(x)$ is a unit, return $x - f(x)/f'(x)$. The unit hypothesis lets us invert $f'(x)$. -/
noncomputable def newtonStep {R : Type*} [CommRing R] (f : R[X]) (x : R)
    (h_unit : IsUnit ((Polynomial.derivative f).eval x)) : R :=
  x - ↑h_unit.unit⁻¹ * f.eval x

/-- *Newton iteration sequence* starting from $x_0$: $c_0 = x_0$ and $c_{n+1} = c_n -
f(c_n) \cdot \text{Ring.inverse}(f'(c_n))$. We use `Ring.inverse` so that this is total in
$R$ — the value is meaningful when $f'(c_n)$ is a unit. -/
noncomputable def newtonSeq {R : Type*} [CommRing R] (f : R[X]) (x₀ : R) : ℕ → R :=
  fun n => Nat.recOn n x₀ fun _ b => b - f.eval b * Ring.inverse ((Polynomial.derivative f).eval b)
