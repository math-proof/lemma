/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Structure.v1.Atlas.ArithmeticGeometry.code.Varieties.Part2
variable (k : Type*) [Field k]


/-- The domain of definition of a rational map. -/
def RationalMap.dom {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : RationalMap k m n X Y) : Set (AffineSpace_k k m) :=
  ratMapDom k m n X φ.denoms

/-- The underlying partial function of a rational map. -/
def RationalMap.toFun {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : RationalMap k m n X Y)
    (P : AffineSpace_k k m) : AffineSpace_k k n :=
  ratMapEval k m n φ.nums φ.denoms P


/-- Every affine morphism is a rational map (with all denominators equal to $1$). -/
def AffineMorphism.toRationalMap {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineMorphism k m n X Y) :
    RationalMap k m n X Y where
  nums := φ.polys
  denoms := fun _ => 1
  denoms_ne_zero := fun _ => one_ne_zero
  dom_open := by
    rw [ratMapDom_of_denom_one]
    exact ⟨Set.Subset.refl X, Set.univ, @isOpen_univ _ (zariskiTopology k m),
      (Set.inter_univ X).symm⟩
  dom_dense := by
    rw [ratMapDom_of_denom_one]
    intro x hx
    rw [@mem_closure_iff _ (zariskiTopology k m)]
    intro U hU hxU
    exact ⟨x, hxU, hx⟩
  maps_to := by
    intro P hP
    rw [ratMapEval_eq_polyMapEval_of_denom_one]
    exact φ.maps_to P hP.1

/-- A rational map is regular if its domain of definition is the entire source variety. -/
def RationalMap.IsRegular {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : RationalMap k m n X Y) : Prop :=
  φ.dom k = X

/-- Convert a regular rational map to an affine morphism, given an explicit choice of polynomials agreeing with $\varphi$ on $X$. -/
def RationalMap.toAffineMorphism {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : RationalMap k m n X Y) (hreg : φ.IsRegular)
    (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (hpolys : ∀ P ∈ X, polyMapEval k m n polys P = ratMapEval k m n φ.nums φ.denoms P) :
    AffineMorphism k m n X Y where
  polys := polys
  maps_to := by
    intro P hP
    rw [hpolys P hP]
    have hdom : P ∈ ratMapDom k m n X φ.denoms := by rw [show ratMapDom k m n X φ.denoms = X from hreg]; exact hP
    exact φ.maps_to P hdom

/-- A rational function $\mathrm{num}/\mathrm{denom}$ is regular at $P \in X$ if some equivalent representation $g/h$ has $g(P) \neq 0$, modulo the vanishing ideal of $X$. -/
def IsRegularAtPoint {m : ℕ} (X : Set (AffineSpace_k k m))
    (num denom : MvPolynomial (Fin m) (AlgebraicClosure k))
    (P : AffineSpace_k k m) : Prop :=
  P ∈ X ∧ ∃ (g h : MvPolynomial (Fin m) (AlgebraicClosure k)),
    MvPolynomial.eval P g ≠ 0 ∧
    g * num - h * denom ∈ MvPolynomial.vanishingIdeal (AlgebraicClosure k) X

/-- The domain of definition of a rational function $\mathrm{num}/\mathrm{denom}$ on $X$. -/
def RationalFunctionDom {m : ℕ} (X : Set (AffineSpace_k k m))
    (num denom : MvPolynomial (Fin m) (AlgebraicClosure k)) : Set (AffineSpace_k k m) :=
  {P ∈ X | ∃ (g h : MvPolynomial (Fin m) (AlgebraicClosure k)),
    MvPolynomial.eval P g ≠ 0 ∧
    g * num - h * denom ∈ MvPolynomial.vanishingIdeal (AlgebraicClosure k) X}

/-- A rational function $\mathrm{num}/\mathrm{denom}$ lies in the coordinate ring of $X$ if it is congruent to a polynomial modulo the vanishing ideal. -/
def RationalFunctionLiesInCoordinateRing {m : ℕ} (X : Set (AffineSpace_k k m))
    (num denom : MvPolynomial (Fin m) (AlgebraicClosure k)) : Prop :=
  ∃ poly : MvPolynomial (Fin m) (AlgebraicClosure k),
    num - poly * denom ∈ MvPolynomial.vanishingIdeal (AlgebraicClosure k) X


/-- A rational map $\varphi : X \dashrightarrow Y$ is dominant if its image is Zariski-dense in $Y$. -/
def RationalMap.IsDominant {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : RationalMap k m n X Y) : Prop :=
  Y ⊆ @closure _ (zariskiTopology k n) (φ.toFun k '' φ.dom)

/-- The domain on which the composition $\varphi \circ \psi$ of rational maps is defined. -/
def RationalMap.compDom {m n r : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    {Z : Set (AffineSpace_k k r)}
    (φ : RationalMap k n r Y Z) (ψ : RationalMap k m n X Y) :
    Set (AffineSpace_k k m) :=
  {P ∈ ψ.dom | ψ.toFun k P ∈ φ.dom}

/-- Two affine varieties $X, Y$ are birationally equivalent if there exist dominant rational maps $\varphi : X \dashrightarrow Y$ and $\psi : Y \dashrightarrow X$ that are mutually inverse where both compositions are defined. -/
def IsBirationallyEquivalent {m n : ℕ}
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) : Prop :=
  ∃ (φ : RationalMap k m n X Y) (ψ : RationalMap k n m Y X),
    φ.IsDominant k ∧ ψ.IsDominant k ∧
    (∀ P ∈ RationalMap.compDom k ψ φ,
      ψ.toFun k (φ.toFun k P) = P) ∧
    (∀ P ∈ RationalMap.compDom k φ ψ,
      φ.toFun k (ψ.toFun k P) = P)

/-- A strict chain $V_0 \subsetneq V_1 \subsetneq \cdots \subsetneq V_d = V$ of affine subvarieties of $V$. -/
def IsStrictVarietyChain {n : ℕ} (V : Set (AffineSpace_k k n)) (d : ℕ)
    (chain : Fin (d + 1) → Set (AffineSpace_k k n)) : Prop :=
  (∀ i, IsAffineVariety k n (chain i)) ∧
  (∀ i j, i < j → chain i ⊂ chain j) ∧
  chain ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = V

/-- The geometric dimension of an affine variety $V$ is the supremum of $d$ for which there exists a strict chain of affine subvarieties of length $d$ ending at $V$. -/
def geometricDim {n : ℕ} (V : Set (AffineSpace_k k n)) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : ∃ chain, IsStrictVarietyChain k V d chain), (d : ℕ∞)

