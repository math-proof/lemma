/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RiemannRoch
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Finsupp

open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily

/-- Structure capturing the residue-field surjection at each place. For each
place $p \in P$, `degPlace p` is the $k$-degree of the residue field
$\mathcal{O}_p / \mathfrak{m}_p$, and `φ D p₀` is a surjective $k$-linear map
from $A(D+p_0)$ onto $\mathcal{O}_{p_0}/\mathfrak{m}_{p_0}$ whose kernel is
exactly $A(D)$ — packaging the ingredient needed for Lemma 22.8. -/
class HasResidueFieldSurjection (P : Type*) (F : Type*) (k : Type*)
    [DecidableEq P] [Field k] [Field F] [Algebra k F]
    (O : P → ValuationSubring F)
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k] where
  degPlace : P → ℕ
  degPlace_pos : ∀ p, 0 < degPlace p
  φ : ∀ (D : P → ℤ) (p₀ : P),
    ↥(adeleSpace (F := F) (O := O) k (Function.update D p₀ (D p₀ + 1))) →ₗ[k]
    (Fin (degPlace p₀) → k)
  φ_surj : ∀ (D : P → ℤ) (p₀ : P), Function.Surjective (φ D p₀)
  φ_ker : ∀ (D : P → ℤ) (p₀ : P),
    LinearMap.ker (φ D p₀) =
      Submodule.comap
        (adeleSpace (F := F) (O := O) k (Function.update D p₀ (D p₀ + 1))).subtype
        (adeleSpace (F := F) (O := O) k D)

/-- The residue field $\mathcal{O}_p/\mathfrak{m}_p$ at a place $p$ is a
$k$-algebra via the composition $k \to \mathcal{O}_p \twoheadrightarrow
\mathcal{O}_p/\mathfrak{m}_p$. -/
noncomputable instance residueFieldAlgebra {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)] (p : P) :
    Algebra k (IsLocalRing.ResidueField ↥(O p)) :=
  letI : Algebra k ↥(O p) :=
    ((algebraMap k F).codRestrict (O p).toSubring
      (fun c => ConstantField.algebraMap_mem (k := k) (O := O) p c)).toAlgebra
  (IsLocalRing.residue ↥(O p) |>.comp (algebraMap k ↥(O p))).toAlgebra

/-- The *degree* $\deg p = [\mathcal{O}_p / \mathfrak{m}_p : k]$ of a place
$p$, defined as the $k$-dimension of the residue field. -/
noncomputable def placeDegree {P : Type*} {F : Type*} {k : Type*}
    [DecidableEq P] [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k] : P → ℕ := fun p =>
  Module.finrank k (IsLocalRing.ResidueField ↥(O p))

/-- $k$-linear projection of an adele onto its $p_0$-component: the map
$\alpha \mapsto \alpha(p_0)$ from the adele ring to $F$. -/
noncomputable def adeleComponentMap {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)]
    (p₀ : P) : FunctionFieldAdeleRing F P O →ₗ[k] F where
  toFun α := α p₀
  map_add' α β := by
    show (α + β) p₀ = α p₀ + β p₀
    rfl
  map_smul' c α := by
    show (c • α) p₀ = c • (α p₀)
    rw [FunctionFieldAdeleRing.smul_apply]
    simp only [Algebra.smul_def]

/-- The composed surjection
$A(D + p_0) \xrightarrow{\alpha \mapsto \alpha(p_0)} F \xrightarrow{\varphi}
k^{\deg p_0}$ realizing the residue-field surjection at the place $p_0$. -/
noncomputable def adeleDivisorDeg {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [DiscreteValuationFamily P F k]
    [DecidableEq P] [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [HasResidueFieldSurjection P F k O] (D : P →₀ ℤ) : ℤ :=
  D.sum (fun p n => n * (HasResidueFieldSurjection.degPlace (F := F) (k := k) (O := O) p : ℤ))

section ChainFormula

variable {R : Type*} [DivisionRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Pullback of $A(A)$ to $A(B)$ as a $k$-submodule: the comap of $A(A)$
along the inclusion $A(B) \hookrightarrow $ adeles. -/
noncomputable abbrev adeleComap (A B : P → ℤ) :
    Submodule k (↥(adeleSpace (F := F) (O := O) k B)) :=
  Submodule.comap (adeleSpace (F := F) (O := O) k B).subtype
    (adeleSpace (F := F) (O := O) k A)

/-- Combinatorial distance between divisors: $\sum_p (B - A)(p)$, truncated to
$\mathbb{N}$. Used as a strong-induction measure in the proof of Lemma 22.8. -/
noncomputable def divisorDistance (A B : P →₀ ℤ) : ℕ :=
  ((B - A).sum (fun _ n => n)).toNat
