/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/SphereCuttingBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.SphereCuttingBound

@[expose] public section

set_option maxHeartbeats 400000

open Set


namespace SphereArrangement

/-- The underlying point set of a sphere: $\{x \in \mathbb{R}^3 : \|x - c\| = r\}$. -/
def Sphere3.toSet (S : Sphere3) : Set R3 :=
  Metric.sphere S.center S.radius

/-- The union $\bigcup_i S_i$ of a finite family of spheres in $\mathbb{R}^3$. -/
def sphereUnion (spheres : Fin n → Sphere3) : Set R3 :=
  ⋃ i, (spheres i).toSet

/-- Number of connected components of the complement of $\bigcup_i S_i$ in $\mathbb{R}^3$. -/
noncomputable def numComponentsComplement (spheres : Fin n → Sphere3) : ℕ :=
  Nat.card (ConnectedComponents (↥(sphereUnion spheres)ᶜ))

end SphereArrangement
