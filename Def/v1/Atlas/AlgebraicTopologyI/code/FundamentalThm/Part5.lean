/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Theorem.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part4


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Resolution

variable {Z : C}

/-- Degree-one component of the chain homotopy to zero: lift the corrected morphism
`f.f 1 - d ≫ liftHomotopyZeroZero f comm` along `d : Q₂ ⟶ Q₁` using exactness of `Q` in
positive degree and projectivity of `P.complex.X 1`. -/
def liftHomotopyZeroOne {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    P.complex.X 1 ⟶ Q.complex.X 2 :=
  (Q.exact_succ 0).liftFromProjective
    (f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
            liftHomotopyZeroZero_comp, sub_self])

/-- Inductive step in building the chain homotopy to zero: given chain homotopy data in degrees
`n` and `n+1`, produce the next degree-`n+2` piece via exactness of `Q` in positive degree and
projectivity of `P.complex.X (n+2)`. -/
def liftHomotopyZeroSucc {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
    P.complex.X (n + 2) ⟶ Q.complex.X (n + 3) :=
  (Q.exact_succ (n + 1)).liftFromProjective
    (f.f (n + 2) - P.complex.d _ _ ≫ g') (by simp [w])

/-- Any chain map `f : P → Q` from a projective resolution to a resolution that becomes zero
after composing with the augmentation `Q.π` is chain-homotopic to zero, by assembling the
degree-zero, degree-one, and inductive degree-`n+2` components. -/
def liftHomotopyZero {Y Z : C}
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    Homotopy f 0 :=
  Homotopy.mkInductive _ (liftHomotopyZeroZero f comm) (by simp)
    (liftHomotopyZeroOne f comm) (by simp) fun n ⟨g, g', w⟩ =>
    ⟨liftHomotopyZeroSucc f n g g' w, by simp⟩

/-- Uniqueness half of Theorem 22.1 (Fundamental Theorem of Homological Algebra):
any two chain maps `g, h : P.complex ⟶ Q.complex` lifting the same `f : Y ⟶ Z` are chain
homotopic. -/
def liftHomotopy {Y Z : C} (f : Y ⟶ Z)
    {P : ProjectiveResolution Y} {Q : Resolution Z}
    (g h : P.complex ⟶ Q.complex)
    (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) :
    Homotopy g h :=
  Homotopy.equivSubZero.symm (liftHomotopyZero _ (by simp [g_comm, h_comm]))

end Resolution
end FundamentalThm
end
