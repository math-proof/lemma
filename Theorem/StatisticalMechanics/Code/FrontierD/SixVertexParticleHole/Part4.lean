/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part3
open Finset Matrix


namespace StatMech.FrontierD

@[simp] theorem sixVertexSectorParticleHoleEquiv_apply_val
    {N n : ℕ} (hn : n ≤ N) (x : SixVertexSector N n) :
    ((sixVertexSectorParticleHoleEquiv N n hn x : SixVertexSector N (N - n)) :
      Finset (Fin N)) = (x : Finset (Fin N))ᶜ :=
  rfl

@[simp] theorem sixVertexSectorRow_particleHole {N n : ℕ} (hn : n ≤ N)
    (x : SixVertexSector N n) (i : Fin N) :
    sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x) i =
      !sixVertexSectorRow x i := by
  simp [sixVertexSectorRow]

theorem sixVertexSectorPrefixCount_add_complement {N n : ℕ}
    (x : SixVertexSector N n) (k : Fin N) :
    sixVertexSectorPrefixCount x k +
      sixVertexSectorPrefixCount (sixVertexSectorComplement x) k = k.val + 1 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.Iic k) (fun j : Fin N => j ∈ (x : Finset (Fin N)))
  have hfirst :
      (Finset.Iic k).filter (fun j => j ∈ (x : Finset (Fin N))) =
        (x : Finset (Fin N)).filter (fun j => j ≤ k) := by
    ext j
    simp [and_comm]
  have hsecond :
      (Finset.Iic k).filter (fun j => ¬j ∈ (x : Finset (Fin N))) =
        ((sixVertexSectorComplement x : SixVertexSector N (N - n)) :
          Finset (Fin N)).filter (fun j => j ≤ k) := by
    ext j
    simp [sixVertexSectorComplement, and_comm]
  rw [hfirst, hsecond, Fin.card_Iic] at h
  exact h

theorem sixVertexSectorPrefixForward_complement {N n : ℕ}
    (x y : SixVertexSector N n) (h : SixVertexSectorPrefixForward x y) :
    SixVertexSectorPrefixForward (sixVertexSectorComplement y)
      (sixVertexSectorComplement x) := by
  intro k
  have hx := sixVertexSectorPrefixCount_add_complement x k
  have hy := sixVertexSectorPrefixCount_add_complement y k
  have hxy := h k
  omega

theorem sixVertexSectorPrefixForward_particleHole_iff {N n : ℕ}
    (hn : n ≤ N) (x y : SixVertexSector N n) :
    SixVertexSectorPrefixForward
        (sixVertexSectorParticleHoleEquiv N n hn y)
        (sixVertexSectorParticleHoleEquiv N n hn x) ↔
      SixVertexSectorPrefixForward x y := by
  change SixVertexSectorPrefixForward (sixVertexSectorComplement y)
      (sixVertexSectorComplement x) ↔ SixVertexSectorPrefixForward x y
  constructor
  · intro h k
    have hx := sixVertexSectorPrefixCount_add_complement x k
    have hy := sixVertexSectorPrefixCount_add_complement y k
    have hxy := h k
    omega
  · exact sixVertexSectorPrefixForward_complement x y

theorem sixVertexInterlaced_particleHole_imp {N n : ℕ} (hn : n ≤ N)
    (x y : SixVertexSector N n)
    (h : SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    SixVertexInterlaced
      (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x))
      (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) := by
  rcases h with hxy | hyx
  · right
    apply sixVertexForwardInterlaced_of_positions
    apply sixVertexPositionsForwardInterlaced_of_prefix
    exact sixVertexSectorPrefixForward_complement x y
      (sixVertexSectorPrefixForward_of_positions x y
        (sixVertexPositionsForwardInterlaced_of_forward x y hxy))
  · left
    apply sixVertexForwardInterlaced_of_positions
    apply sixVertexPositionsForwardInterlaced_of_prefix
    exact sixVertexSectorPrefixForward_complement y x
      (sixVertexSectorPrefixForward_of_positions y x
        (sixVertexPositionsForwardInterlaced_of_forward y x hyx))

theorem sixVertexInterlaced_particleHole_iff {N n : ℕ} (hn : n ≤ N)
    (x y : SixVertexSector N n) :
    SixVertexInterlaced
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x))
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) ↔
      SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) := by
  constructor
  · intro h
    rcases h with hxy | hyx
    · right
      apply sixVertexForwardInterlaced_of_positions
      apply sixVertexPositionsForwardInterlaced_of_prefix
      apply (sixVertexSectorPrefixForward_particleHole_iff hn y x).mp
      exact sixVertexSectorPrefixForward_of_positions _ _
        (sixVertexPositionsForwardInterlaced_of_forward _ _ hxy)
    · left
      apply sixVertexForwardInterlaced_of_positions
      apply sixVertexPositionsForwardInterlaced_of_prefix
      apply (sixVertexSectorPrefixForward_particleHole_iff hn x y).mp
      exact sixVertexSectorPrefixForward_of_positions _ _
        (sixVertexPositionsForwardInterlaced_of_forward _ _ hyx)
  · exact sixVertexInterlaced_particleHole_imp hn x y

theorem sixVertexRowDistance_particleHole {N n : ℕ} (hn : n ≤ N)
    (x y : SixVertexSector N n) :
    sixVertexRowDistance
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x))
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) =
      sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) := by
  unfold sixVertexRowDistance
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    sixVertexSectorRow_particleHole]
  cases sixVertexSectorRow x i <;> cases sixVertexSectorRow y i <;> decide

theorem sixVertexSectorRow_injective {N n : ℕ} :
    Function.Injective (@sixVertexSectorRow N n) := by
  intro x y h
  apply Subtype.ext
  ext i
  have hi := congrFun h i
  simp only [sixVertexSectorRow_apply] at hi
  simpa using hi

theorem sixVertexSectorTransfer_particleHole {N n : ℕ} (hn : n ≤ N)
    (c : ℝ) (x y : SixVertexSector N n) :
    sixVertexSectorTransfer N (N - n) c
        (sixVertexSectorParticleHoleEquiv N n hn x)
        (sixVertexSectorParticleHoleEquiv N n hn y) =
      sixVertexSectorTransfer N n c x y := by
  let e := sixVertexSectorParticleHoleEquiv N n hn
  have heinj : Function.Injective
      (fun x : SixVertexSector N n => sixVertexSectorRow (e x)) :=
    sixVertexSectorRow_injective.comp e.injective
  by_cases hxy : x = y
  · subst y
    simp [sixVertexSectorTransfer, sixVertexTransfer]
  · have hexy : sixVertexSectorRow (e x) ≠ sixVertexSectorRow (e y) := by
      intro h
      exact hxy (heinj h)
    have hrowxy : sixVertexSectorRow x ≠ sixVertexSectorRow y := by
      intro h
      exact hxy (sixVertexSectorRow_injective h)
    simp only [sixVertexSectorTransfer, sixVertexTransfer_apply]
    rw [if_neg hrowxy, if_neg hexy]
    by_cases hinter : SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y)
    · have hinter' := (sixVertexInterlaced_particleHole_iff hn x y).mpr hinter
      simp [hinter, hinter', sixVertexRowDistance_particleHole hn x y]
    · have hinter' : ¬SixVertexInterlaced
          (sixVertexSectorRow (e x)) (sixVertexSectorRow (e y)) := by
        exact fun h => hinter ((sixVertexInterlaced_particleHole_iff hn x y).mp h)
      change ¬SixVertexInterlaced
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x))
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) at hinter'
      simp [hinter, hinter']

theorem sixVertexSectorTransfer_reindex_particleHole {N n : ℕ} (hn : n ≤ N)
    (c : ℝ) :
    Matrix.reindex (sixVertexSectorParticleHoleEquiv N n hn)
        (sixVertexSectorParticleHoleEquiv N n hn)
        (sixVertexSectorTransfer N n c) =
      sixVertexSectorTransfer N (N - n) c := by
  let e := sixVertexSectorParticleHoleEquiv N n hn
  ext x y
  rw [Matrix.reindex_apply]
  change sixVertexSectorTransfer N n c (e.symm x) (e.symm y) = _
  rw [← sixVertexSectorTransfer_particleHole hn c (e.symm x) (e.symm y)]
  simp [e]

theorem matrix_hasEigenvalue_of_equiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A : Matrix α α ℝ) (B : Matrix β β ℝ)
    (hentry : ∀ x y, B (e x) (e y) = A x y) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) μ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin B) μ := by
  classical
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hveig : A *ᵥ (fun i => v i) = μ • (fun i => v i) := by
    have hvT := Module.End.mem_eigenspace_iff.mp hv.1
    have hvT' := congrArg WithLp.ofLp hvT
    simpa [Matrix.ofLp_toLpLin] using hvT'
  let w : EuclideanSpace ℝ β := WithLp.toLp 2 fun j => v (e.symm j)
  have hwne : w ≠ 0 := by
    intro hw0
    apply hv.2
    apply WithLp.ofLp_injective 2
    funext i
    have hi := congrArg (fun q : EuclideanSpace ℝ β => q (e i)) hw0
    simpa [w] using hi
  have hweig : B *ᵥ (fun j => w j) = μ • (fun j => w j) := by
    funext j
    have hvj := congrFun hveig (e.symm j)
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hvj ⊢
    calc
      ∑ z, B j z * w z = ∑ i, B j (e i) * v i := by
        symm
        apply Fintype.sum_equiv e
        intro i
        simp [w]
      _ = ∑ i, A (e.symm j) i * v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hentry]
        simp
      _ = μ * v (e.symm j) := hvj
      _ = μ * w j := by simp [w]
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hwne⟩
  apply WithLp.ofLp_injective 2
  simpa [Matrix.ofLp_toLpLin] using hweig

theorem sixVertexSectorTop_ge_of_hasEigenvalue {N n : ℕ} (hn : n ≤ N)
    (c μ : ℝ)
    (hμ : Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) μ) :
    μ ≤ sixVertexSectorTopEigenvalue N n hn c := by
  classical
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sixVertexSectorTransfer_isHermitian N n c)
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq finrank_euclideanSpace hμ
  rw [← hi]
  exact sixVertexSectorTopEigenvalue_ge N n hn c i


theorem sixVertexSectorTopEigenvalue_particleHole {N n : ℕ} (hn : n ≤ N)
    (c : ℝ) :
    sixVertexSectorTopEigenvalue N (N - n) (Nat.sub_le N n) c =
      sixVertexSectorTopEigenvalue N n hn c := by
  let e := sixVertexSectorParticleHoleEquiv N n hn
  let A := sixVertexSectorTransfer N n c
  let B := sixVertexSectorTransfer N (N - n) c
  apply le_antisymm
  · apply sixVertexSectorTop_ge_of_hasEigenvalue hn
    apply matrix_hasEigenvalue_of_equiv e.symm B A
    · intro x y
      have h := sixVertexSectorTransfer_particleHole hn c (e.symm x) (e.symm y)
      simpa [e] using h.symm
    · exact sixVertexSectorTop_hasEigenvalue N (N - n) (Nat.sub_le N n) c
  · apply sixVertexSectorTop_ge_of_hasEigenvalue (Nat.sub_le N n)
    apply matrix_hasEigenvalue_of_equiv e A B
    · exact sixVertexSectorTransfer_particleHole hn c
    · exact sixVertexSectorTop_hasEigenvalue N n hn c

theorem sixVertex_half_add_le {N r : ℕ} (hN : Even N)
    (hr : r ≤ N / 2) : N / 2 + r ≤ N := by
  obtain ⟨k, rfl⟩ := hN
  omega


end StatMech.FrontierD
