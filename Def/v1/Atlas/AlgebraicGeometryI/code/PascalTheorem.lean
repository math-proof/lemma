/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.PascalCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PascalCurves
import Structure.v1.Atlas.AlgebraicGeometryI.code.PascalTheorem
open Polynomial

set_option autoImplicit false


namespace ProjectivePascal

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

end ProjectivePascal
