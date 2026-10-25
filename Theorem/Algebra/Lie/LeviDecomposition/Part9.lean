/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part8
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

@[simp] theorem leviQuotientMk_apply
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (x : L) :
    leviQuotientMk I x = LieSubmodule.Quotient.mk x := by
  rfl

theorem leviQuotientMk_surjective
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) : Function.Surjective (leviQuotientMk I) := by
  intro y
  obtain ⟨x, hx⟩ := LieSubmodule.Quotient.surjective_mk' I y
  exact ⟨x, (leviQuotientMk_apply I x).trans hx⟩

@[simp] theorem leviQuotientMk_ker
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) : (leviQuotientMk I).ker = I := by
  ext x
  rw [LieHom.mem_ker, leviQuotientMk_apply]
  exact LieSubmodule.Quotient.mk_eq_zero (N := I)

theorem levi_isSolvable_of_ker_quotient
    {K L L' : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (f : L →ₗ⁅K⁆ L')
    (hf : Function.Surjective f) [LieAlgebra.IsSolvable f.ker]
    [LieAlgebra.IsSolvable L'] : LieAlgebra.IsSolvable L := by
  obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K L'
  obtain ⟨l, hl⟩ := LieAlgebra.IsSolvable.solvable K f.ker
  apply LieAlgebra.IsSolvable.mk (R := K) (L := L) (k := l + k)
  change LieAlgebra.derivedSeriesOfIdeal K L (l + k) ⊤ = ⊥
  rw [LieAlgebra.derivedSeriesOfIdeal_add]
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hl
  apply le_bot_iff.mp
  rw [← hl]
  apply LieAlgebra.derivedSeriesOfIdeal_mono
  rw [← LieIdeal.map_eq_bot_iff]
  rw [LieIdeal.derivedSeries_map_eq k hf, hk]

end LeviDecomposition
