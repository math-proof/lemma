/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionFold.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionGeometry.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Def.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionFold.Part4
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section Domain

variable (K : Finset (Site d)) (i j : Fin d) (hij : i ≠ j) (c : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingDiagonalReflect i j c x ∈ K)

theorem isingDiagonalDomainGlue_reflect
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    isingCfgEquiv (isingDiagonalDomainReflectEquiv K i j hij c hK)
        (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) =
      isingDiagonalDomainGlue K i j hij c hK boundary upper lower := by
  funext x
  by_cases hp : isingDiagonalDomainPlane K i j c x
  · have hfixed := isingDiagonalDomainReflect_fixed K i j hij c hK hp
    simp [isingCfgEquiv, isingDiagonalDomainGlue, hp, hfixed]
  · by_cases hl : isingDiagonalDomainLower K i j c x
    · have hpR := isingDiagonalDomainReflect_not_plane K i j hij c hK hp
      have hlR := isingDiagonalDomainReflect_not_lower_of_lower
        K i j hij c hK hl
      have hRR : isingDiagonalDomainReflectEquiv K i j hij c hK
          (isingDiagonalDomainReflectEquiv K i j hij c hK x) = x :=
        (isingDiagonalDomainReflectEquiv K i j hij c hK).left_inv x
      simp [isingCfgEquiv, isingDiagonalDomainGlue, hp, hl, hpR, hlR, hRR]
    · have hlR := isingDiagonalDomainReflect_lower_of_upper
        K i j hij c hK hp hl
      have hpR := isingDiagonalDomainReflect_not_plane K i j hij c hK hp
      simp [isingCfgEquiv, isingDiagonalDomainGlue, hp, hl, hpR, hlR]

theorem isingDiagonalDomain_no_lower_upper_edge
    {x y : freeDomainVertices K}
    (hxy : (freeDomainGraph K).Adj x y) (hij0 : i ≠ j) :
    ¬ ((isingDiagonalDomainLower K i j c x ∧
          ¬ isingDiagonalDomainLower K i j c y ∧
          ¬ isingDiagonalDomainPlane K i j c y) ∨
        (isingDiagonalDomainLower K i j c y ∧
          ¬ isingDiagonalDomainLower K i j c x ∧
          ¬ isingDiagonalDomainPlane K i j c x)) := by
  rintro (⟨hxl, hyl, hyp⟩ | ⟨hyl, hxl, hxp⟩)
  · apply diagonalPlane_separates_adjacent i j hij0 c hxy hxl
    unfold isingDiagonalDomainLower at hyl
    unfold isingDiagonalDomainPlane at hyp
    omega
  · apply diagonalPlane_separates_adjacent i j hij0 c hxy.symm hyl
    unfold isingDiagonalDomainLower at hxl
    unfold isingDiagonalDomainPlane at hxp
    omega

theorem isingDiagonalDomain_bond_four_identity
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c))
    (e : Sym2 (freeDomainVertices K))
    (he : e ∈ (freeDomainGraph K).edgeFinset) :
    bond (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) e +
        bond (isingDiagonalDomainGlue K i j hij c hK boundary upper lower) e =
      bond (isingDiagonalDomainGlue K i j hij c hK boundary lower lower) e +
        bond (isingDiagonalDomainGlue K i j hij c hK boundary upper upper) e := by
  induction e using Sym2.ind with
  | _ x y =>
      have hxy : (freeDomainGraph K).Adj x y := by
        rwa [SimpleGraph.mem_edgeFinset] at he
      have hn := isingDiagonalDomain_no_lower_upper_edge
        K i j c hxy hij
      simp only [bond_mk]
      by_cases hxp : isingDiagonalDomainPlane K i j c x
      · by_cases hyp : isingDiagonalDomainPlane K i j c y
        · simp [spin, isingDiagonalDomainGlue, hxp, hyp]
        · by_cases hyl : isingDiagonalDomainLower K i j c y
          · simp [spin, isingDiagonalDomainGlue, hxp, hyp, hyl]
          · simp [spin, isingDiagonalDomainGlue, hxp, hyp, hyl]
            ring
      · by_cases hxl : isingDiagonalDomainLower K i j c x
        · by_cases hyp : isingDiagonalDomainPlane K i j c y
          · simp [spin, isingDiagonalDomainGlue, hxp, hxl, hyp]
          · have hyl : isingDiagonalDomainLower K i j c y := by
              by_contra hyl
              exact hn (Or.inl ⟨hxl, hyl, hyp⟩)
            simp [spin, isingDiagonalDomainGlue, hxp, hxl, hyp, hyl]
        · by_cases hyp : isingDiagonalDomainPlane K i j c y
          · simp [spin, isingDiagonalDomainGlue, hxp, hxl, hyp]
            ring
          · have hyl : ¬ isingDiagonalDomainLower K i j c y := by
              intro hyl
              exact hn (Or.inr ⟨hyl, hxl, hxp⟩)
            simp [spin, isingDiagonalDomainGlue, hxp, hxl, hyp, hyl]
            ring

theorem isingDiagonalDomain_hamiltonian_midpoint
    (boundary : ConfigSpace (IsingDiagonalDomainPlane K i j c))
    (lower upper : ConfigSpace (IsingDiagonalDomainLower K i j c)) :
    2 * hamiltonian (freeDomainGraph K) 0
        (isingDiagonalDomainGlue K i j hij c hK boundary lower upper) =
      hamiltonian (freeDomainGraph K) 0
          (isingDiagonalDomainGlue K i j hij c hK boundary lower lower) +
        hamiltonian (freeDomainGraph K) 0
          (isingDiagonalDomainGlue K i j hij c hK boundary upper upper) := by
  let qlu := isingDiagonalDomainGlue K i j hij c hK boundary lower upper
  let qul := isingDiagonalDomainGlue K i j hij c hK boundary upper lower
  let qll := isingDiagonalDomainGlue K i j hij c hK boundary lower lower
  let quu := isingDiagonalDomainGlue K i j hij c hK boundary upper upper
  have hreflect : hamiltonian (freeDomainGraph K) 0 qlu =
      hamiltonian (freeDomainGraph K) 0 qul := by
    have h := hamiltonian_isingCfgEquiv (freeDomainGraph K) (freeDomainGraph K)
      (isingDiagonalDomainReflectEquiv K i j hij c hK)
      (isingDiagonalDomainReflectEquiv_adj K i j hij c hK) 0 qlu
    have hcfg := isingDiagonalDomainGlue_reflect
      K i j hij c hK boundary lower upper
    change isingCfgEquiv
        (isingDiagonalDomainReflectEquiv K i j hij c hK) qlu = qul at hcfg
    rw [hcfg] at h
    exact h.symm
  have hfour :
      (∑ e ∈ (freeDomainGraph K).edgeFinset, bond qlu e) +
          ∑ e ∈ (freeDomainGraph K).edgeFinset, bond qul e =
        (∑ e ∈ (freeDomainGraph K).edgeFinset, bond qll e) +
          ∑ e ∈ (freeDomainGraph K).edgeFinset, bond quu e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e he =>
      isingDiagonalDomain_bond_four_identity K i j hij c hK
        boundary lower upper e he
  unfold hamiltonian at hreflect ⊢
  simp only [zero_mul, sub_zero] at hreflect ⊢
  dsimp only [qlu, qul, qll, quu] at hfour hreflect ⊢
  linarith

end Domain
end StatMech.FrontierA
