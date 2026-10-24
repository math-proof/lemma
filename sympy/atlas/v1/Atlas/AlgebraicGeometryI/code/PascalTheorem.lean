/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.PascalCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PascalCurves

open Polynomial

set_option autoImplicit false

namespace ProjectivePascal

/-- A projective conic on P^2: a function on k^3 that is homogeneous of degree 2. -/
structure Conic (k : Type*) [Field k] where
  eval : (Fin 3 → k) → k
  homog : ∀ (c : k) (v : Fin 3 → k), eval (c • v) = c ^ 2 * eval v

/-- A projective line on P^2: a k-linear function k^3 → k. -/
structure Line (k : Type*) [Field k] where
  eval : (Fin 3 → k) → k
  map_add : ∀ (v w : Fin 3 → k), eval (v + w) = eval v + eval w
  map_smul : ∀ (c : k) (v : Fin 3 → k), eval (c • v) = c * eval v

/-- A conic is irreducible if its defining function is not a product of two linear
forms (i.e. it is not the union of two projective lines). -/
def Conic.IsIrreducible {k : Type*} [Field k] (Q : Conic k) : Prop :=
  ∀ (L₁ L₂ : Line k), Q.eval ≠ fun v => L₁.eval v * L₂.eval v

/-- The point P (in k^3) lies on the conic Q if Q vanishes on P. -/
def OnConic {k : Type*} [Field k] (Q : Conic k) (P : Fin 3 → k) : Prop :=
  Q.eval P = 0

/-- A line passes through a pair of points P_1, P_2 if it vanishes on both and is not
identically zero. -/
def Line.ThroughPair {k : Type*} [Field k] (L : Line k)
    (P₁ P₂ : Fin 3 → k) : Prop :=
  L.eval P₁ = 0 ∧ L.eval P₂ = 0 ∧ L.eval ≠ 0

/-- The point R is an intersection of two lines L_1 and L_2 if it lies on both and is
a nonzero vector. -/
def IsIntersectionOf {k : Type*} [Field k]
    (R : Fin 3 → k) (L₁ L₂ : Line k) : Prop :=
  L₁.eval R = 0 ∧ L₂.eval R = 0 ∧ R ≠ 0

/-- Three points are collinear if there exists a nonzero line passing through all three. -/
def AreCollinear {k : Type*} [Field k]
    (R₁ R₂ R₃ : Fin 3 → k) : Prop :=
  ∃ (L : Line k), L.eval ≠ 0 ∧ L.eval R₁ = 0 ∧ L.eval R₂ = 0 ∧ L.eval R₃ = 0

/-- Six points (as vectors in k^3) are pairwise projectively distinct if no two
represent the same point of projective space. -/
def PairwiseProjectivelyDistinct {k : Type*} [Field k]
    (P : Fin 6 → (Fin 3 → k)) : Prop :=
  ∀ i j : Fin 6, i ≠ j → ¬∃ (c : k), c ≠ 0 ∧ P i = c • P j

/-- All six points are nonzero vectors (so represent honest projective points). -/
def AllNonzero {k : Type*} [Field k]
    (P : Fin 6 → (Fin 3 → k)) : Prop :=
  ∀ i : Fin 6, P i ≠ 0

/-- All six points lie on the conic Q. -/
def AllOnConic {k : Type*} [Field k]
    (Q : Conic k) (P : Fin 6 → (Fin 3 → k)) : Prop :=
  ∀ i : Fin 6, OnConic Q (P i)

/-- Bezout-style configuration lemma for the projective Pascal theorem: for six points
on an irreducible conic Q with the triangle of opposite sides configuration, there is
a scalar t and a linear form L such that the cubic ABC - t(A'B'C') equals QL. -/
end ProjectivePascal

namespace PascalTheoremConics

/-- A projective conic given by an irreducible monic polynomial of degree 2. -/
structure ProjectiveConic (k : Type*) [Field k] where
  poly : Polynomial k
  irred : Irreducible poly
  monic : poly.Monic
  deg : poly.natDegree = 2

/-- An inscribed hexagon in a conic: three "sides" and three "opposite sides", each a
polynomial of degree ≤ 1, together with a scalar t making the cubic difference
non-coprime to the conic. -/
structure InscribedHexagon (k : Type*) [Field k] (conic : ProjectiveConic k) where
  sideA : Polynomial k
  sideB : Polynomial k
  sideC : Polynomial k
  oppA : Polynomial k
  oppB : Polynomial k
  oppC : Polynomial k
  sideA_deg : sideA.natDegree ≤ 1
  sideB_deg : sideB.natDegree ≤ 1
  sideC_deg : sideC.natDegree ≤ 1
  oppA_deg : oppA.natDegree ≤ 1
  oppB_deg : oppB.natDegree ≤ 1
  oppC_deg : oppC.natDegree ≤ 1
  t : k
  not_coprime : ¬ IsCoprime conic.poly
    (sideA * sideB * sideC - Polynomial.C t * (oppA * oppB * oppC))

/-- The cubic associated to an inscribed hexagon: side_A·side_B·side_C - t·opp_A·opp_B·opp_C. -/
noncomputable def InscribedHexagon.cubicP {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic) : Polynomial k :=
  hex.sideA * hex.sideB * hex.sideC - Polynomial.C hex.t * (hex.oppA * hex.oppB * hex.oppC)

/-- The Pascal line of a hexagon: the quotient of the hexagon cubic by the conic. -/
noncomputable def InscribedHexagon.pascalLine {k : Type*} [Field k]
    {conic : ProjectiveConic k} (hex : InscribedHexagon k conic) : Polynomial k :=
  hex.cubicP /ₘ conic.poly
