/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.Pairings.Part2
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Lattice
import Def.v1.Atlas.NumberTheoryI.code.PairingsTheorems.Part2
open Submodule LinearMap Module


noncomputable section

section DirectSumDualLattice

theorem dualSubmodule_isALattice
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (M : Submodule A V) (hM : IsALattice A K V M) :
    IsALattice A K V (BilinForm.dualSubmodule B M) := by
  classical
  have hs : ⊤ ≤ span K (M : Set V) := hM.span_eq_top ▸ le_refl _
  obtain ⟨ι, _, _, b, h_sub⟩ : ∃ (ι : Type _) (_ : DecidableEq ι) (_ : Fintype ι)
      (b : Basis ι K V), Set.range b ⊆ (M : Set V) := by
    let b := Basis.ofSpan hs
    have : Finite _ := Finite.finite_basis b
    exact ⟨_, inferInstance, Fintype.ofFinite _, b, Basis.ofSpan_subset hs⟩
  have hle : span A (Set.range b) ≤ M := span_le.mpr h_sub
  have h_le : BilinForm.dualSubmodule B M ≤
      span A (Set.range (BilinForm.dualBasis B hB b)) := by
    rw [← BilinForm.dualSubmodule_span_of_basis B hB b]
    exact dualSubmodule_antitone B hle
  have hN_fg : (span A (Set.range (BilinForm.dualBasis B hB b))).FG :=
    ⟨Set.Finite.toFinset (Set.finite_range _), by rw [Set.Finite.coe_toFinset]⟩
  obtain ⟨s, hs_span⟩ := hM.fg
  constructor

  · haveI := isNoetherian_of_fg_of_noetherian _ hN_fg
    rw [show BilinForm.dualSubmodule B M =
      Submodule.map (span A (Set.range (BilinForm.dualBasis B hB b))).subtype
        (Submodule.comap (span A (Set.range (BilinForm.dualBasis B hB b))).subtype
          (BilinForm.dualSubmodule B M)) from by
      rw [Submodule.map_comap_subtype]; exact (inf_eq_right.mpr h_le).symm]
    exact (IsNoetherian.noetherian _).map _

  · rw [eq_top_iff]
    intro w _
    obtain ⟨⟨d, hd_mem⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors A) (s.image (fun m => B w m))
    have h_mem : d • w ∈ BilinForm.dualSubmodule B M := by
      rw [BilinForm.mem_dualSubmodule]
      intro y hy
      rw [← hs_span] at hy
      refine Submodule.span_induction
        (fun x (hx : x ∈ (s : Set V)) => ?_) ?_ (fun x y _ _ hx hy => ?_)
        (fun a x _ hx => ?_) hy
      · simp only [map_smul_of_tower, smul_apply, Algebra.smul_def]
        obtain ⟨a, ha⟩ := hd (B w x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
        rw [Submodule.mem_one]
        exact ⟨a, by simpa [Algebra.smul_def] using ha⟩
      · simp only [map_zero]; exact zero_mem _
      · simp only [map_add] at *; exact add_mem hx hy
      · rw [map_smul_of_tower]; exact Submodule.smul_mem _ a hx
    have hd_ne : algebraMap A K d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd_mem
    have hw : w = (algebraMap A K d)⁻¹ • (d • w) := by
      rw [smul_comm, ← smul_assoc]
      simp only [Algebra.smul_def, mul_inv_cancel₀ hd_ne, one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h_mem)

theorem thm_5_12_surjective
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (M : Submodule A V) (hM : IsALattice A K V M) :
    Function.Surjective (BilinForm.dualSubmoduleToDual B M) := by
  intro f
  have hs : ⊤ ≤ Submodule.span K (M : Set V) := hM.span_eq_top ▸ le_refl _
  classical
  let b : Basis _ K V := Basis.ofSpan hs
  have hb_mem : ∀ i, (b i : V) ∈ M :=
    fun i => Basis.ofSpan_subset hs ⟨i, rfl⟩
  haveI : Fintype _ := FiniteDimensional.fintypeBasisIndex b
  let g : V →ₗ[K] K := b.constr K (fun i => algebraMap A K (f ⟨b i, hb_mem i⟩))
  have hg_basis : ∀ i, g (b i) = algebraMap A K (f ⟨b i, hb_mem i⟩) :=
    fun i => b.constr_basis (S := K) _ i
  let x : V := (BilinForm.toDual B hB).symm g
  have hBx : ∀ v, (B x) v = g v := by
    intro v
    have : BilinForm.toDual B hB x = g := LinearEquiv.apply_symm_apply _ g
    exact congr_fun (congr_arg DFunLike.coe this) v

  have key : ∀ (m : V) (hm : m ∈ M), g m = algebraMap A K (f ⟨m, hm⟩) := by
    intro m hm
    have hm_eq : m = ∑ i, (b.repr m i) • b i := (b.sum_repr m).symm
    obtain ⟨d, hd_int⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors A) (Finset.univ.image (fun i => b.repr m i))


    have hd_ci : ∀ i, IsLocalization.IsInteger A ((d : A) • b.repr m i) :=
      fun i => hd_int _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    choose a ha using hd_ci


    have hdm_eq : (d : A) • m = ∑ i, a i • b i := by
      conv_lhs => rw [show (d : A) • m = algebraMap A K (d : A) • m from
        (algebraMap_smul K (d : A) m).symm]
      rw [hm_eq, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, ← mul_smul]
      conv_lhs => rw [mul_comm]
      rw [← Algebra.smul_def, ← ha i, algebraMap_smul]

    have hdm_mem : (d : A) • m ∈ M := M.smul_mem (d : A) hm
    have hai_mem : ∀ i, (a i) • b i ∈ M :=
      fun i => M.smul_mem (a i) (hb_mem i)

    have hf_dm : f ⟨(d : A) • m, hdm_mem⟩ = (d : A) * f ⟨m, hm⟩ := by
      rw [show (⟨(d : A) • m, hdm_mem⟩ : ↥M) = (d : A) • ⟨m, hm⟩ from rfl,
          map_smul, smul_eq_mul]

    have hf_sum : f ⟨∑ i, (a i) • b i, M.sum_mem (fun i _ => hai_mem i)⟩ =
        ∑ i, a i * f ⟨b i, hb_mem i⟩ := by
      have h2 : (⟨∑ i, (a i) • b i, M.sum_mem (fun i _ => hai_mem i)⟩ : ↥M) = ∑ i, a i • ⟨b i, hb_mem i⟩ := by

        ext; simp
      rw [h2, map_sum]; congr 1; ext i; rw [map_smul, smul_eq_mul]

    have hf_eq : f ⟨(d : A) • m, hdm_mem⟩ =
        f ⟨∑ i, (a i) • b i, M.sum_mem (fun i _ => hai_mem i)⟩ := by
      congr 1; ext; exact hdm_eq

    have arith : (d : A) * f ⟨m, hm⟩ = ∑ i, a i * f ⟨b i, hb_mem i⟩ := by
      rw [← hf_dm, hf_eq, hf_sum]

    have arith_K : algebraMap A K (d : A) * algebraMap A K (f ⟨m, hm⟩) =
        ∑ i, algebraMap A K (a i) * algebraMap A K (f ⟨b i, hb_mem i⟩) := by
      rw [← map_mul, arith, map_sum]; congr 1; ext i; exact map_mul _ _ _

    have lhs_eq : algebraMap A K (d : A) * g m =
        ∑ i, algebraMap A K (a i) * algebraMap A K (f ⟨b i, hb_mem i⟩) := by

      rw [← smul_eq_mul, ← g.map_smul]


      rw [show algebraMap A K (d : A) • m = (d : A) • m from algebraMap_smul K _ m]
      rw [hdm_eq]


      simp only [map_sum, map_smul_of_tower]
      congr 1; ext i
      rw [hg_basis, Algebra.smul_def]

    have both_eq : algebraMap A K (d : A) * g m =
        algebraMap A K (d : A) * algebraMap A K (f ⟨m, hm⟩) := by
      rw [lhs_eq, arith_K]
    have hd_ne : algebraMap A K (d : A) ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero d.2 (IsFractionRing.injective A K (by simp [h]))
    exact mul_left_cancel₀ hd_ne both_eq
  have hx_mem : x ∈ BilinForm.dualSubmodule B M := by
    intro m hm; rw [hBx m, key m hm]
    exact ⟨f ⟨m, hm⟩, by simp [Algebra.algebraMap_eq_smul_one]⟩
  exact ⟨⟨x, hx_mem⟩, by
    ext ⟨m, hm⟩
    apply IsFractionRing.injective A K
    change algebraMap A K (BilinForm.dualSubmoduleParing B ⟨x, hx_mem⟩ ⟨m, hm⟩) = _
    rw [BilinForm.dualSubmoduleParing_spec, hBx, key m hm]⟩

theorem thm_5_12
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : B.Nondegenerate)
    (M : Submodule A V) (hM : IsALattice A K V M) :
    IsALattice A K V (BilinForm.dualSubmodule B M) ∧
    Function.Bijective (BilinForm.dualSubmoduleToDual B M) := by
  refine ⟨dualSubmodule_isALattice B hB M hM, ?_⟩
  exact ⟨thm_5_12_injective B hB M hM.span_eq_top,
         thm_5_12_surjective B hB M hM⟩

end DirectSumDualLattice
end
