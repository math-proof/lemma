/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.AffineWeylBook.Part2
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Set.Card
import Structure.v1.Atlas.Buildings.code.AffineCoxeter.CanonicalMetric
set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Set


noncomputable section

namespace AffineCoxeter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [instance] AffineCoxeterComplex.decEq

/-- The canonical normalised distance on an affine Coxeter complex: the Euclidean
distance scaled so that every closed chamber has diameter $1$. -/
def normalizedDist (A : AffineCoxeterComplex E) (x y : E) : ℝ :=
  euclideanDist x y / A.chamberDiameter

/-- The inverse of a simplicial complex isomorphism, obtained by swapping forward and
backward morphisms. -/
def SimplicialComplexIso.symm {V' W' : Type*} [DecidableEq V'] [DecidableEq W']
    {K : SimplicialComplex V'} {L : SimplicialComplex W'}
    (φ : SimplicialComplexIso K L) : SimplicialComplexIso L K where
  toMorphism := φ.invMorphism
  invMorphism := φ.toMorphism
  left_inv := φ.right_inv
  right_inv := φ.left_inv

/-- Main quantitative form: any affine map $f$ extending $\varphi$ on the vertex set
is a similitude with factor $\mu$, where $A'.\mathrm{chamberDiameter}
= \mu \cdot A.\mathrm{chamberDiameter}$. -/
def canonicalDist (chamberDiam : ℝ) (_hD : chamberDiam > 0) (x y : E) : ℝ :=
  euclideanDist x y / chamberDiam

end AffineCoxeter
end
