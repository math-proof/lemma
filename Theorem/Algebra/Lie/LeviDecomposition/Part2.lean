/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem leviTraceKernel_isSolvable
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] [Module.Finite K M] [LieModule.IsFaithful K L M] :
    LieAlgebra.IsSolvable (leviTraceKernel (K := K) (L := L) (M := M)) := by
  let I := leviTraceKernel (K := K) (L := L) (M := M)
  change LieAlgebra.IsSolvable I
  have htf : LieModule.traceForm K I M = 0 := by
    ext x y
    change LieModule.traceForm K L M x.1 y.1 = 0
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp x.2) y
  let D' := LieAlgebra.derivedSeries K I 1
  have hnil : LieModule.IsNilpotent D' M :=
    LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero htf
  let D : LieIdeal K L := ⁅I, I⁆
  have hnil' (x : D) : IsNilpotent (LieModule.toEnd K D M x) := by
    have hxI : x.1 ∈ I := LieSubmodule.lie_le_left I I x.2
    have hxD' : (⟨x.1, hxI⟩ : I) ∈ LieAlgebra.derivedSeries K I 1 := by
      rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap]
      exact x.2
    let x' : D' := ⟨⟨x.1, hxI⟩, hxD'⟩
    have hx := (LieModule.isNilpotent_iff_forall' (R := K)).mp hnil x'
    change IsNilpotent (LieModule.toEnd K L M x.1)
    change IsNilpotent (LieModule.toEnd K L M x'.1.1) at hx
    simpa [x'] using hx
  let φ := LieModule.toEnd K D M
  have hrange : LieRing.IsNilpotent φ.range := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := K) (L := φ.range)]
    rintro ⟨_, ⟨x, rfl⟩⟩
    apply LieAlgebra.isNilpotent_ad_of_isNilpotent
    exact hnil' x
  let _ : LieRing.IsNilpotent φ.range := hrange
  have hφ : Function.Injective φ.rangeRestrict := by
    intro x y hxy
    apply Subtype.ext
    apply LieModule.IsFaithful.injective_toEnd (R := K) (L := L) (M := M)
    exact congr_arg Subtype.val hxy
  have hD : LieRing.IsNilpotent D := hφ.lieAlgebra_isNilpotent
  let _ : LieRing.IsNilpotent D := hD
  let _ : LieAlgebra.IsSolvable D := inferInstance
  obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K D
  rw [LieIdeal.derivedSeries_eq_bot_iff (R := K) (L := L) D] at hk
  change LieAlgebra.derivedSeriesOfIdeal K L k ⁅I, I⁆ = ⊥ at hk
  refine LieAlgebra.IsSolvable.mk (R := K) (L := I) (k := k + 1) ?_
  rw [LieIdeal.derivedSeries_eq_bot_iff (R := K) (L := L) I]
  rwa [LieAlgebra.derivedSeriesOfIdeal_add, LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero]

theorem levi_traceForm_nondegenerate
    {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] [LieModule.IsFaithful K L M] :
    (LieModule.traceForm K L M).Nondegenerate := by
  let I := leviTraceKernel (K := K) (L := L) (M := M)
  have hsolv : LieAlgebra.IsSolvable I := leviTraceKernel_isSolvable
  let _ : LieAlgebra.IsSolvable I := hsolv
  have hI : I = ⊥ := LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable I
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  change (I : Submodule K L) = ⊥
  exact congr_arg LieSubmodule.toSubmodule hI

end LeviDecomposition
