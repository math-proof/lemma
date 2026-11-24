module
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.AdjointAction.Derivation
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Engel
public import Mathlib.Algebra.Lie.LieTheorem
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Algebra.Lie.SemiDirect
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Set.Finite.List
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NoncommRing
public import Def.Algebra.Lie.LeviDecomposition.Part15
public import Theorem.Fin.EqSum_SMul.of.Basis
public import Theorem.Algebra.Lie.Ado.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

attribute [local instance 100] LieRing.ofAssociativeRing

/-!
# Ado's theorem

This file proves Ado's theorem over fields of characteristic zero. It builds finite-dimensional
representations from quotients of universal enveloping algebras, then uses the Levi decomposition.
-/


namespace MathlibExt.Algebra.Lie.LandmarkWanted

def adoWordsLt
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (n : ℕ) : Set (adoUEA K L) :=
  {u | ∃ w : List (Fin d), w.length < n ∧ adoWord b w = u}

def adoModWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (Q : Ideal (adoUEA K L)) (b : Module.Basis (Fin d) K L) (n : ℕ) :
    Submodule K (adoUEA K L) :=
  (Q : Submodule (adoUEA K L) (adoUEA K L)).restrictScalars K ⊔
    Submodule.span K (adoWordsLt b n)

def adoAllWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) : Set (adoUEA K L) :=
  Set.range (adoWord b)

def adoQuotientRepresentation
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M]
    (ρ : L →ₗ⁅K⁆ Module.End K M) (P : Submodule K M)
    (hP : ∀ x, P ≤ P.comap (ρ x)) :
    L →ₗ⁅K⁆ Module.End K (M ⧸ P) where
  toLinearMap :=
    { toFun := fun x => P.mapQ P (ρ x) (hP x)
      map_add' := by
        intro x y
        ext m
        change (Submodule.Quotient.mk (ρ (x + y) m) : M ⧸ P) =
          Submodule.Quotient.mk (ρ x m) + Submodule.Quotient.mk (ρ y m)
        simp
      map_smul' := by
        intro c x
        ext m
        change (Submodule.Quotient.mk (ρ (c • x) m) : M ⧸ P) =
          c • Submodule.Quotient.mk (ρ x m)
        simp }
  map_lie' := by
    intro x y
    ext m
    change (Submodule.Quotient.mk (ρ ⁅x, y⁆ m) : M ⧸ P) =
      Submodule.Quotient.mk (ρ x (ρ y m)) -
        Submodule.Quotient.mk (ρ y (ρ x m))
    rw [LieHom.map_lie ρ]
    change Submodule.Quotient.mk ((ρ x (ρ y m)) - (ρ y (ρ x m))) = _
    rfl

noncomputable def adoSemidirectEquivOfIsCompl
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (H : LieSubalgebra K L)
    (hc : IsCompl I.toSubmodule H.toSubmodule) :
    (I ⋊⁅(adoIdealAd I).comp H.incl⁆ H) ≃ₗ⁅K⁆ L where
  __ := (LieAlgebra.SemiDirectSum.toProdl ((adoIdealAd I).comp H.incl)).trans
    (I.toSubmodule.prodEquivOfIsCompl H.toSubmodule hc)
  map_lie' := by
    intro x y
    change
      (⁅(x.left : L), (y.left : L)⁆ + ⁅(x.right : L), (y.left : L)⁆ -
          ⁅(y.right : L), (x.left : L)⁆ : L) + ⁅(x.right : L), (y.right : L)⁆ =
        ⁅(x.left : L) + x.right, (y.left : L) + y.right⁆
    simp only [lie_add, add_lie]
    have hskew : -⁅(y.right : L), (x.left : L)⁆ =
        ⁅(x.left : L), (y.right : L)⁆ := by
      rw [lie_skew]
    rw [sub_eq_add_neg, hskew]
    abel

def adoRestrictIdeal
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (N : LieSubmodule K L M) (I : LieIdeal K L) : LieSubmodule K I M where
  carrier := N
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' := N.smul_mem'
  lie_mem hm := N.lie_mem hm

end MathlibExt.Algebra.Lie.LandmarkWanted
