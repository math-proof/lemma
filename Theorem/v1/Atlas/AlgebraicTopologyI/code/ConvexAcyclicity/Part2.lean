/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ConvexAcyclicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Def.v1.Atlas.AlgebraicTopologyI.code.ConvexAcyclicity.Part2
open Finset BigOperators


namespace AlgebraicTopologyI

noncomputable section

/-- The zeroth face of the cone $c(\sigma)$ on a simplex $\sigma$ recovers $\sigma$ itself,
because the $0$-th face of $\Delta^{n+2}$ corresponds to the bottom face $t_0 = 0$ of the cone. -/
theorem coneSimplex_face_zero (p q n : ℕ)
    (σ : SingularSimplex (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))) :
    SingularSimplex.face 0 (coneSimplex p q (n + 1) σ) = σ := by
  apply ContinuousMap.ext
  intro t
  simp only [SingularSimplex.face, ContinuousMap.comp_apply, coneSimplex, ContinuousMap.prodMk,
    coneSimplex₁, ContinuousMap.coe_mk, coneRawSimplex]

  have h0 : (faceInclusion (n + 1) 0 t).1 0 = 0 := by
    simp [faceInclusion]

  have hne : (faceInclusion (n + 1) 0 t).1 0 ≠ 1 := by rw [h0]; exact one_ne_zero.symm

  have h_rescale : rescaleTail (n + 1) (faceInclusion (n + 1) 0 t) = t := by
    simp only [rescaleTail, dif_neg hne]
    ext i
    simp only [h0, sub_zero, div_one]
    simp [faceInclusion]
  simp only [h0, zero_mul, zero_add, sub_zero, one_mul, h_rescale]
  simp

/-- Inserting a value at position `i.succ` in a tuple leaves the first coordinate unchanged,
since the insertion position is strictly positive. -/
lemma insertNth_succ_zero' (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → ℝ) :
    @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 f 0 = f 0 := by
  conv_lhs => rw [show (0 : Fin (n + 3)) = i.succ.succAbove 0 from
    (Fin.succ_succAbove_zero i).symm]
  exact @Fin.insertNth_apply_succAbove (n + 2) (fun _ => ℝ) i.succ 0 f 0

/-- Compatibility of `Fin.insertNth` with the successor map: inserting at `i.succ` on the
`succ`-shifted index equals inserting at `i` on the shifted tail. -/
lemma insertNth_succ_succ' (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → ℝ)
    (j : Fin (n + 2)) :
    @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 f (Fin.succ j) =
    @Fin.insertNth (n + 1) (fun _ => ℝ) i 0 (fun k : Fin (n + 1) => f (Fin.succ k)) j := by
  by_cases hji : j = i
  · subst hji
    rw [@Fin.insertNth_apply_same (n + 1) (fun _ => ℝ)]
    exact @Fin.insertNth_apply_same (n + 2) (fun _ => ℝ) j.succ 0 f
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (y := i) hji
    subst hk
    rw [@Fin.insertNth_apply_succAbove (n + 1) (fun _ => ℝ) i 0 _ k]
    conv_lhs => rw [show Fin.succ (i.succAbove k) = i.succ.succAbove (Fin.succ k) from
      (Fin.succ_succAbove_succ i k).symm]
    exact @Fin.insertNth_apply_succAbove (n + 2) (fun _ => ℝ) i.succ 0 f (Fin.succ k)

/-- Compatibility of `rescaleTail` with the $i$-th face inclusion (for $i > 0$): rescaling after
inclusion equals inclusion after rescaling. This is the key combinatorial identity behind
`coneSimplex_face_succ`. -/
lemma rescaleTail_faceInclusion_succ (n : ℕ) (i : Fin (n + 2))
    (t : ↥(stdSimplex ℝ (Fin (n + 2)))) (ht : t.1 0 ≠ 1) :
    rescaleTail (n + 1) ⟨Fin.insertNth i.succ 0 t.1,
      faceMap_mem_stdSimplex (n + 1) i.succ t.1 t.2⟩ =
    ⟨Fin.insertNth i 0 (rescaleTail n t).1,
      faceMap_mem_stdSimplex n i (rescaleTail n t).1 (rescaleTail n t).2⟩ := by
  have ht0_eq : @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 t.1 0 = t.1 0 :=
    insertNth_succ_zero' n i t.1
  have h1 : @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 t.1 0 ≠ 1 := by rw [ht0_eq]; exact ht
  apply Subtype.ext
  funext k
  simp only [rescaleTail, dif_neg h1, dif_neg ht]
  rw [insertNth_succ_succ' n i t.1 k, ht0_eq]
  by_cases hki : k = i
  · subst hki
    simp
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (y := i) hki
    subst hj
    simp [@Fin.insertNth_apply_succAbove (n + 1) (fun _ => ℝ)]

/-- For positive face indices `i.succ`, the face of the cone equals the cone of the face:
$d_{i+1}(c(\sigma)) = c(d_i \sigma)$. This together with `coneSimplex_face_zero` is what makes
`coneChain` a chain homotopy. -/
theorem coneSimplex_face_succ (p q n : ℕ) (i : Fin (n + 2))
    (σ : SingularSimplex (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))) :
    SingularSimplex.face i.succ (coneSimplex p q (n + 1) σ) =
      coneSimplex p q n (SingularSimplex.face i σ) := by
  apply ContinuousMap.ext
  intro t
  simp only [SingularSimplex.face, ContinuousMap.comp_apply, coneSimplex, coneSimplex₁,
    ContinuousMap.prod_eval, faceInclusion, ContinuousMap.coe_mk]
  have ht0_eq : @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 t.1 0 = t.1 0 :=
    insertNth_succ_zero' n i t.1

  by_cases ht : t.1 0 = 1
  ·
    apply Prod.ext <;> apply Subtype.ext <;> funext j <;>
      simp only [coneRawSimplex, ContinuousMap.comp_apply, ContinuousMap.coe_mk, ht0_eq, ht] <;>
      ring
  ·
    have h_rescale := rescaleTail_faceInclusion_succ n i t ht
    apply Prod.ext <;> apply Subtype.ext <;> funext j <;>
      simp only [coneRawSimplex, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ht0_eq, h_rescale]


/-- The chain-level cone formula $d \circ h + h \circ d = \mathrm{id}$ on chains in
$\Delta^p \times \Delta^q$: the boundary of the cone of $c$ equals $c$ minus the cone of its
boundary. This realises `coneChain` as a chain contraction. -/
theorem coneSimplex_boundary (p q n : ℕ)
    (c : SingularChains (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))) :
    boundaryMap (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))
      (coneChain p q (n + 1) c) =
    c - coneChain p q n (boundaryMap n
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) c) := by

  induction c using FreeAbelianGroup.induction_on with
  | zero =>
    show (boundaryMap _ _) ((coneChain p q (n + 1)) 0) =
      0 - (coneChain p q n) ((boundaryMap _ _) 0)
    simp only [AddMonoidHom.map_zero, sub_zero]
  | of σ =>

    change boundaryMap (n + 1) _ ((FreeAbelianGroup.map (coneSimplex p q (n + 1)))
      (FreeAbelianGroup.of σ)) = _
    rw [FreeAbelianGroup.map_of_apply]

    change (FreeAbelianGroup.lift (fun τ =>
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (SingularSimplex.face i τ)))
      (FreeAbelianGroup.of (coneSimplex p q (n + 1) σ)) = _
    erw [FreeAbelianGroup.lift_apply_of]

    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul]

    rw [coneSimplex_face_zero]

    simp_rw [coneSimplex_face_succ p q n _ σ]

    simp_rw [show ∀ j : Fin (n + 2), (j.succ : ℕ) = (j : ℕ) + 1 from fun _ => rfl,
      pow_succ, mul_neg_one, neg_smul]

    rw [Finset.sum_neg_distrib]


    rw [sub_eq_add_neg]
    congr 1

    congr 1

    symm
    change (FreeAbelianGroup.map (coneSimplex p q n))
      ((FreeAbelianGroup.lift (fun τ =>
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          FreeAbelianGroup.of (SingularSimplex.face i τ)))
        (FreeAbelianGroup.of σ)) = _
    erw [FreeAbelianGroup.lift_apply_of]
    rw [map_sum]
    congr 1; ext j
    rw [map_zsmul, FreeAbelianGroup.map_of_apply]
  | neg σ ih =>
    have h1 : (coneChain p q (n + 1)) (-FreeAbelianGroup.of σ) =
      -((coneChain p q (n + 1)) (FreeAbelianGroup.of σ)) := map_neg _ _
    have h2 : (boundaryMap n _) (-FreeAbelianGroup.of σ) =
      -((boundaryMap n _) (FreeAbelianGroup.of σ)) := map_neg _ _
    have h3 : (coneChain p q n) (-(boundaryMap n _ (FreeAbelianGroup.of σ))) =
      -((coneChain p q n) ((boundaryMap n _) (FreeAbelianGroup.of σ))) := map_neg _ _
    rw [h1, map_neg, ih, h2, h3]
    simp only [sub_eq_add_neg, neg_neg, neg_add_rev]
    abel
  | add a b iha ihb =>
    have h1 : (coneChain p q (n + 1)) (a + b) =
      (coneChain p q (n + 1)) a + (coneChain p q (n + 1)) b := map_add _ _ _
    have h2 : (boundaryMap n _) (a + b) =
      (boundaryMap n _) a + (boundaryMap n _) b := map_add _ _ _
    have h3 : (coneChain p q n) ((boundaryMap n _) a + (boundaryMap n _) b) =
      (coneChain p q n) ((boundaryMap n _) a) +
      (coneChain p q n) ((boundaryMap n _) b) := map_add _ _ _
    rw [h1, map_add, iha, ihb, h2, h3]
    simp only [sub_eq_add_neg, neg_add_rev]
    abel

/-- Acyclicity of the singular chain complex on a product of standard simplices in positive
degrees: every $(n+1)$-cycle in $\Delta^p \times \Delta^q$ is a boundary. This is the technical
heart of Proposition 5.13 ($S_*(X) \to \mathbf{Z}$ is a chain homotopy equivalence for star-shaped
$X$) for the case of products of simplices. -/
theorem stdSimplex_prod_acyclic (p q n : ℕ)
    (c : SingularChains (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))))
    (hc : boundaryMap n
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) c = 0) :
    ∃ d : SingularChains (n + 2)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))),
      boundaryMap (n + 1)
        (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) d = c := by
  refine ⟨coneChain p q (n + 1) c, ?_⟩
  rw [coneSimplex_boundary p q n c, hc, map_zero, sub_zero]

end
end AlgebraicTopologyI
