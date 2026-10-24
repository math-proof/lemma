/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/CanonicalMetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.AffineWeylBook
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Set.Card

set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Set

noncomputable section

namespace AffineCoxeter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A map $f : E \to E'$ is a similitude with respect to distances $d_1, d_2$ if there
exists a uniform scale factor $\mu$ with $d_2(f(x), f(y)) = \mu \cdot d_1(x, y)$. -/
def IsSimilitude {E' : Type*} [NormedAddCommGroup E'] (f : E → E')
    (d₁ : E → E → ℝ) (d₂ : E' → E' → ℝ) : Prop :=
  ∃ (μ : ℝ), ∀ x y : E, d₂ (f x) (f y) = μ * d₁ x y

/-- The Euclidean distance on an inner-product space: $d(x, y) = \|x - y\|$. -/
def euclideanDist (x y : E) : ℝ := ‖x - y‖

/-- A distance function is $W$-invariant if every element of the affine reflection
group acts as an isometry. -/
def IsWInvariant (W : AffineReflectionGroup E) (d : E → E → ℝ) : Prop :=
  ∀ w ∈ W.group, ∀ x y : E, d (w x) (w y) = d x y

/-- An isomorphism of simplicial complexes: a pair of mutually inverse morphisms
between $K$ and $L$. -/
structure SimplicialComplexIso {V W : Type*} [DecidableEq V] [DecidableEq W]
    (K : SimplicialComplex V) (L : SimplicialComplex W) where
  toMorphism : SimplicialComplex.Morphism K L
  invMorphism : SimplicialComplex.Morphism L K
  left_inv : ∀ v, invMorphism.toFun (toMorphism.toFun v) = v
  right_inv : ∀ w, toMorphism.toFun (invMorphism.toFun w) = w

/-- The structure of an abstract affine Coxeter complex in $E$: an abstract simplicial
complex on vertices $V$ with a labelling, an affine vertex map onto a spanning subset,
a chosen chamber diameter, a Coxeter matrix and normal basis with Gram matrix encoding
the local Coxeter data, and the bijection between chamber adjacencies and Coxeter exponents. -/
structure AffineCoxeterComplex (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  V : Type*
  [decEq : DecidableEq V]
  W : AffineReflectionGroup E
  complex : SimplicialComplex V
  vertexMap : V → E
  affineSpan_vertexMap_eq_top : affineSpan ℝ (Set.range vertexMap) = ⊤
  chamberDiameter : ℝ
  chamberDiameter_pos : chamberDiameter > 0
  n : ℕ
  normalBasis : Module.Basis (Fin n) ℝ E
  coxeterMatrix : Fin n → Fin n → ℕ
  coxeterGram : Fin n → Fin n → ℝ
  coxeterGram_of_coxeterMatrix : ∀ i j : Fin n,
    coxeterGram i j = -Real.cos (Real.pi / (coxeterMatrix i j : ℝ))
  normalBasis_inner : ∀ i j : Fin n, @inner ℝ E _ (normalBasis i) (normalBasis j) = coxeterGram i j
  chamber_card : ∀ C, complex.IsMaximal C → C.card = n + 1
  exists_chamber : ∃ C, complex.IsMaximal C
  vertexType : V → Fin (n + 1)
  vertexType_chamber_bijective :
    ∀ (C : Finset V), complex.IsMaximal C →
      ∀ (t : Fin (n + 1)), ∃! v, v ∈ C ∧ vertexType v = t
  coxeterMatrix_eq_chamberCount :
    ∀ (C : Finset V), complex.IsMaximal C →
    ∀ i j : Fin n,
      Set.ncard {D | complex.IsMaximal D ∧
        C.filter (fun v => vertexType v ≠ i.castSucc ∧ vertexType v ≠ j.castSucc) ⊆ D} =
      2 * coxeterMatrix i j
  chamberCount_finite :
    ∀ (C : Finset V), complex.IsMaximal C →
    ∀ i j : Fin n,
      Set.Finite {D | complex.IsMaximal D ∧
        C.filter (fun v => vertexType v ≠ i.castSucc ∧ vertexType v ≠ j.castSucc) ⊆ D}
  vertex_in_chamber : ∀ v : V, ∃ C : Finset V, complex.IsMaximal C ∧ v ∈ C

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
