/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/InvariantTheoryLemmas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part7
public import Theorem.Rat.EqProjectToH.of.Given
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Polynomial.Subring
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

set_option linter.unusedSectionVars false


noncomputable section

open MvPolynomial Finset

section ReynoldsOperator

variable {k : Type*} [Field k] [CharZero k]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def reynoldsOperator :
    MvPolynomial ι k →ₗ[k] MvPolynomial ι k where
  toFun h := (Fintype.card G : k)⁻¹ • Finset.univ.sum fun g => (algAct g) h
  map_add' x y := by
    simp only [map_add, Finset.sum_add_distrib, smul_add]
  map_smul' r x := by
    simp only [map_smul, Finset.smul_sum, smul_comm r, RingHom.id_apply]

def positiveInvariantIdeal :
    Ideal (MvPolynomial ι k) :=
  Ideal.span {f | f ∈ polynomialInvariantSubalgebra k G ι algAct ∧
    f ≠ 0 ∧ MvPolynomial.totalDegree f > 0}

def normPoly (x : MvPolynomial ι k) : Polynomial (MvPolynomial ι k) :=
  Finset.univ.prod (fun g : G => Polynomial.X - Polynomial.C ((algAct g) x))

def IsMinimalGeneratingSet (r : ℕ) (f : Fin r → MvPolynomial ι k)
    (I : Ideal (MvPolynomial ι k)) : Prop :=
  I = Ideal.span (Set.range f) ∧
    ∀ j : Fin r, f j ∉ Ideal.span (Set.range (fun i : {i : Fin r // i ≠ j} => f i.val))

def jacobianMatrixAt (y : ι → MvPolynomial ι k) (u : ι → k) : Matrix ι ι k :=
  fun i j => MvPolynomial.eval u ((MvPolynomial.pderiv j) (y i))

def IsProductOfReflections (g : G) : Prop :=
  ∃ (n : ℕ) (reflections : Fin n → G),
    (∀ i, IsComplexReflection (ρ (reflections i))) ∧
    g = (List.ofFn reflections).prod

end ReynoldsOperator
end
