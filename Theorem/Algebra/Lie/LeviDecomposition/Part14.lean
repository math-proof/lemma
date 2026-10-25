/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.Algebra.Lie.LeviDecomposition.Part13
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem levi_exists_of_abelian_radical
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] (hR : IsLieAbelian (LieAlgebra.radical K L)) :
    ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
      ((LieAlgebra.radical K L : Submodule K L) + (S : Submodule K L) = ⊤) ∧
      ((LieAlgebra.radical K L : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
  let R := LieAlgebra.radical K L
  let V := leviHomScalarMaps (L := L) R
  let P : LieSubmodule K L V := ⁅R, ⊤⁆
  obtain ⟨f, hf, hfP⟩ := levi_abelian_radical_map (K := K) (L := L)
  have hPrange : P.toSubmodule ≤ LinearMap.range (leviTheta R f) :=
    levi_lie_le_range_theta R hR f hf
  let H := leviStabilizer R f
  have hRH : (R : Submodule K L) + (H : Submodule K L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxP : ⁅x, f⁆ ∈ P := hfP x
    obtain ⟨r, hr⟩ := hPrange hxP
    rw [Submodule.add_eq_sup, Submodule.mem_sup]
    refine ⟨r.1, r.2, x - r.1, ?_, ?_⟩
    · change ⁅x - r.1, f⁆ = 0
      rw [sub_lie]
      change ⁅r.1, f⁆ = ⁅x, f⁆ at hr
      rw [hr, sub_self]
    · abel
  let q := leviQuotientMk R
  let qH : H →ₗ⁅K⁆ L ⧸ R := q.comp H.incl
  have hqH : Function.Surjective qH := by
    intro y
    obtain ⟨x, hx⟩ := leviQuotientMk_surjective R y
    have hxTop : x ∈ (R : Submodule K L) + (H : Submodule K L) := by
      rw [hRH]
      trivial
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hxTop
    obtain ⟨r, hr, h, hh, hrh⟩ := hxTop
    refine ⟨⟨h, hh⟩, ?_⟩
    change q h = y
    have hqr : q r = 0 := by
      rw [← LieHom.mem_ker, leviQuotientMk_ker]
      exact hr
    calc
      q h = q (r + h) := by rw [map_add, hqr, zero_add]
      _ = q x := congrArg q hrh
      _ = y := hx
  have hcentral : ∀ x ∈ qH.ker, ∀ y : H, ⁅x, y⁆ = 0 := by
    intro x hx y
    have hxq : q x.1 = 0 := by
      exact LieHom.mem_ker.mp hx
    have hxR : x.1 ∈ R := by
      rw [← leviQuotientMk_ker R, LieHom.mem_ker]
      exact hxq
    have hxStab : ⁅x.1, f⁆ = 0 := x.2
    have hmap := congrArg Subtype.val hxStab
    have heval := congrArg (fun g : L →ₗ[K] R ↦ g y.1) hmap
    change ⁅x.1, f.1 y.1⁆ - f.1 ⁅x.1, y.1⁆ = 0 at heval
    have hab : ⁅(⟨x.1, hxR⟩ : R), f.1 y.1⁆ = 0 :=
      hR.trivial ⟨x.1, hxR⟩ (f.1 y.1)
    have hab' : ⁅x.1, f.1 y.1⁆ = 0 := hab
    rw [hab', zero_sub] at heval
    have hfxy : f.1 ⁅x.1, y.1⁆ = 0 := neg_eq_zero.mp heval
    have hxyR : ⁅x.1, y.1⁆ ∈ R := lie_mem_left K L R x.1 y.1 hxR
    have hfix := hf (⟨⁅x.1, y.1⁆, hxyR⟩ : R)
    apply Subtype.ext
    have hzero := congrArg Subtype.val hfxy
    have hfix' := congrArg Subtype.val hfix
    rw [hfix'] at hzero
    exact hzero
  let _ : LieAlgebra.IsSemisimple K (L ⧸ R) :=
    levi_quotient_radical_isSemisimple
  obtain ⟨T, hTsemi, hTsum, hTinf⟩ :=
    levi_split_central_kernel qH hqH hcentral
  let S := T.map H.incl
  have hHincl : Function.Injective H.incl := by
    intro x y h
    exact Subtype.ext h
  let eTS : T ≃ₗ⁅K⁆ S := LieSubalgebra.equivMapOfInjective H.incl T hHincl
  let _ : LieAlgebra.IsKilling K T := inferInstance
  let _ : LieAlgebra.IsKilling K S := LieAlgebra.isKilling_of_equiv eTS
  let _ : LieAlgebra.IsSemisimple K S := inferInstance
  refine ⟨S, inferInstance, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hxTop : x ∈ (R : Submodule K L) + (H : Submodule K L) := by
      rw [hRH]
      trivial
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hxTop
    obtain ⟨r, hr, h, hh, hrh⟩ := hxTop
    have hhTop : (⟨h, hh⟩ : H) ∈
        (qH.ker : Submodule K H) + (T : Submodule K H) := by
      rw [hTsum]
      trivial
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hhTop
    obtain ⟨z, hz, t, ht, hzt⟩ := hhTop
    change x ∈ (R : Submodule K L) + (S : Submodule K L)
    rw [Submodule.add_eq_sup, Submodule.mem_sup]
    refine ⟨r + z.1, R.add_mem hr ?_, t.1, ?_, ?_⟩
    · have hzq : q z.1 = 0 := LieHom.mem_ker.mp hz
      have hzker : z.1 ∈ (leviQuotientMk R).ker := LieHom.mem_ker.mpr hzq
      change z.1 ∈ R
      rwa [leviQuotientMk_ker] at hzker
    · exact (LieSubalgebra.mem_map H.incl T t.1).mpr ⟨t, ht, rfl⟩
    · have hhval : z.1 + t.1 = h := congrArg Subtype.val hzt
      rw [← hrh, ← hhval]
      abel
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨t, ht, htval⟩ := (LieSubalgebra.mem_map H.incl T x).mp hx.2
    have htR : t.1 ∈ R := by
      change H.incl t ∈ R
      rw [htval]
      exact hx.1
    have htKer : t ∈ qH.ker := by
      rw [LieHom.mem_ker]
      change q t.1 = 0
      rw [← LieHom.mem_ker, leviQuotientMk_ker]
      exact htR
    have htBot : t ∈ (⊥ : Submodule K H) := by
      rw [← hTinf]
      exact ⟨htKer, ht⟩
    have htZero : t = 0 := by simpa using htBot
    change x = 0
    rw [← htval, htZero, map_zero]

end LeviDecomposition
