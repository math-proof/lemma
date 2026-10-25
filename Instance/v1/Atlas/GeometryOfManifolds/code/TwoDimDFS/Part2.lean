/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/TwoDimDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Theorem.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS
set_option autoImplicit false
set_option maxHeartbeats 800000


noncomputable section

/-- Polynomial forms on $\mathbb{R}^2$ assemble into a `DifferentialFormSpace`, giving a
two-dimensional scaffolding (DFS) for the local model of a symplectic surface. -/
noncomputable instance symp2DFS : DifferentialFormSpace Symp2Ω Symp2VF where
  instAddCommGroup := symp2AddCommGroup
  instModule := symp2Module
  fMul := symp2fMul
  wedge1 := symp2wedge1
  d := symp2d
  ι := symp2Iota
  L := symp2L
  d_add := by
    intro p
    match p with
    | 0 => intro α β; simp [symp2d, map_add, Prod.mk_add_mk]
    | 1 => intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩; simp [symp2d, map_add]; ring
    | 2 => intro _ _; rfl
    | _ + 3 => intro _ _; rfl
  d_smul := by
    intro p
    match p with
    | 0 => intro r α; simp [symp2d, Derivation.map_smul, Prod.smul_mk]
    | 1 => intro r ⟨a, b⟩; simp [symp2d, Derivation.map_smul, smul_sub]
    | 2 => intro _ _; rfl
    | _ + 3 => intro _ _; rfl
  d_squared := by
    intro p
    match p with
    | 0 =>
      intro f
      show MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 f) -
           MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 f) = 0
      have : (MvPolynomial.pderiv (0 : Fin 2)) ((MvPolynomial.pderiv (1 : Fin 2)) f) =
             (MvPolynomial.pderiv (1 : Fin 2)) ((MvPolynomial.pderiv (0 : Fin 2)) f) := by
        induction f using MvPolynomial.induction_on with
        | C r => simp
        | add p q hp hq => simp [map_add, hp, hq]
        | mul_X p i hp =>
          simp [MvPolynomial.pderiv_X, Derivation.leibniz]
          rw [hp]
          fin_cases i <;> simp [Pi.single, Function.update] <;> ring
      rw [sub_eq_zero]; exact this
    | 1 => intro ⟨_, _⟩; exact Subsingleton.elim _ _
    | 2 => intro _; exact Subsingleton.elim _ _
    | _ + 3 => intro _; exact Subsingleton.elim _ _
  d_fMul := by
    intro p
    match p with
    | 0 =>
      intro f α
      simp only [symp2d, symp2fMul, symp2wedge1]
      congr 1 <;> simp [Derivation.leibniz] <;> ring
    | 1 =>
      intro f ⟨a, b⟩
      simp only [symp2d, symp2fMul, symp2wedge1]
      simp [Derivation.leibniz]
      ring
    | 2 =>
      intro f α
      exact Subsingleton.elim _ _
    | _ + 3 =>
      intro f α
      exact Subsingleton.elim _ _
  fMul_add_left := by
    intro p
    match p with
    | 0 => intro f g α; simp [symp2fMul, add_mul]
    | 1 => intro f g ⟨a, b⟩; simp [symp2fMul, add_mul, Prod.mk_add_mk]
    | 2 => intro f g h; simp [symp2fMul, add_mul]
    | _ + 3 => intro _ _ _; rfl
  fMul_add_right := by
    intro p
    match p with
    | 0 => intro f α β; simp [symp2fMul, mul_add]
    | 1 => intro f ⟨a₁, b₁⟩ ⟨a₂, b₂⟩; simp [symp2fMul, mul_add, Prod.mk_add_mk]
    | 2 => intro f h₁ h₂; simp [symp2fMul, mul_add]
    | _ + 3 => intro _ _ _; rfl
  fMul_smul := by
    intro p
    match p with
    | 0 => intro r f α; simp [symp2fMul]
    | 1 => intro r f ⟨a, b⟩; simp [symp2fMul, Prod.smul_mk]
    | 2 => intro r f h; simp [symp2fMul]
    | _ + 3 => intro _ _ _; rfl
  wedge1_add_right := by
    intro p
    match p with
    | 0 => intro ⟨f, g⟩ α β; simp [symp2wedge1, mul_add, Prod.mk_add_mk]
    | 1 => intro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ ⟨f₃, g₃⟩; simp [symp2wedge1, mul_add]; ring
    | 2 => intro _ _ _; rfl
    | _ + 3 => intro _ _ _; rfl
  wedge1_smul_right := by
    intro p
    match p with
    | 0 => intro ⟨f, g⟩ r α; simp [symp2wedge1, mul_comm, Algebra.mul_smul_comm, Prod.smul_mk]
    | 1 => intro ⟨f₁, g₁⟩ r ⟨f₂, g₂⟩; simp [symp2wedge1, Algebra.mul_smul_comm, smul_sub]
    | 2 => intro _ _ _; rfl
    | _ + 3 => intro _ _ _; rfl
  ι_add := by
    intro ⟨a, b⟩ p
    match p with
    | 0 => intro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩; simp [symp2Iota, mul_add]; ring
    | 1 => intro h₁ h₂; simp [symp2Iota]; constructor <;> ring
    | 2 => intro _ _; simp [symp2Iota]
    | _ + 3 => intro _ _; rfl
  ι_smul := by
    intro ⟨a, b⟩ p
    match p with
    | 0 => intro r ⟨f, g⟩; simp [symp2Iota]
    | 1 => intro r h; simp [symp2Iota]
    | 2 => intro r _; simp [symp2Iota]
    | _ + 3 => intro _ _; rfl
  ι_fMul := by
    intro ⟨a, b⟩ p
    match p with
    | 0 => intro f ⟨g, h⟩; simp [symp2Iota, symp2fMul]; ring
    | 1 => intro f h; simp [symp2Iota, symp2fMul]; constructor <;> ring
    | 2 => intro f _; simp [symp2Iota, symp2fMul]
    | _ + 3 => intro _ _; rfl
  ι_wedge1 := by
    intro ⟨a, b⟩ p
    match p with
    | 0 => intro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩
           simp [symp2Iota, symp2fMul, symp2wedge1]
           constructor <;> ring
    | 1 => intro ⟨f₁, g₁⟩ h
           simp [symp2Iota, symp2fMul, symp2wedge1]
           ring
    | 2 => intro ⟨f₁, g₁⟩ _
           simp [symp2Iota, symp2fMul, symp2wedge1]
    | _ + 3 => intro _ _; rfl
  ι_squared := by
    intro ⟨a, b⟩ p
    match p with
    | 0 => intro h; simp [symp2Iota]; ring
    | 1 => intro h; simp [symp2Iota]
    | 2 => intro _; simp [symp2Iota]
    | _ + 3 => intro _; exact Subsingleton.elim _ _
  ι_ι_anticomm := by
    intro ⟨a, b⟩ ⟨c, d⟩ p
    match p with
    | 0 => intro h; simp [symp2Iota]; ring
    | 1 => intro h; simp [symp2Iota]
    | 2 => intro _; simp [symp2Iota]
    | _ + 3 => intro _; exact Subsingleton.elim _ _
  L_add := by
    intro X p
    match p with
    | 0 =>
      intro α β
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, map_add]
      ring
    | 1 =>
      intro ⟨α₁, α₂⟩ ⟨β₁, β₂⟩
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, map_add]
      apply Prod.ext <;> simp [Derivation.leibniz] <;> ring
    | 2 =>
      intro α β
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, map_add, add_mul, neg_add]
      ring
    | _ + 3 => intro _ _; rfl
  L_smul := by
    intro X p
    match p with
    | 0 =>
      intro r α
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, Derivation.map_smul, smul_add, Algebra.mul_smul_comm]
    | 1 =>
      intro r ⟨α₁, α₂⟩
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, Derivation.map_smul]
      apply Prod.ext <;> simp [Algebra.mul_smul_comm, smul_add, smul_sub, sub_mul]
    | 2 =>
      intro r α
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, smul_mul_assoc, map_neg,
                 Derivation.map_smul, smul_neg, smul_sub, add_zero,
                 neg_mul]
    | _ + 3 => intro _ _; rfl
  L_zero_eq_ι_d := by
    intro X f; rfl
  L_comm_d := by
    intro X p
    match p with
    | 0 =>
      intro f
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota]
      apply Prod.ext <;> simp [sub_mul] <;> rw [pderiv_comm_poly 0 1 f] <;> ring
    | 1 =>
      intro ⟨α₁, α₂⟩
      obtain ⟨a, b⟩ := X
      unfold symp2L symp2d symp2Iota
      simp only [add_zero]
      simp [Derivation.leibniz, map_add, map_sub, pderiv_comm_poly]
      ring
    | 2 =>
      intro α; exact Subsingleton.elim _ _
    | _ + 3 => intro _; rfl
  L_fMul := by
    intro X p
    match p with
    | 0 =>
      intro f α
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, symp2fMul]
      simp [Derivation.leibniz]
      ring
    | 1 =>
      intro f ⟨α₁, α₂⟩
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, symp2fMul]
      apply Prod.ext <;> simp [Derivation.leibniz] <;> ring
    | 2 =>
      intro f α
      obtain ⟨a, b⟩ := X
      simp only [symp2L, symp2d, symp2Iota, symp2fMul, add_zero]
      simp [Derivation.leibniz, map_neg]
      ring
    | _ + 3 => intro _ _; rfl
  ext_fdα := by
    intro p T hT_add hT_smul hT_gen
    match p with
    | 0 =>


      intro ⟨α₁, α₂⟩
      have hx : symp2fMul (p := 1) α₁ (symp2d (p := 0) (MvPolynomial.X 0)) = (α₁, 0) := by
        simp [symp2fMul, symp2d, MvPolynomial.pderiv_X, Pi.single, Function.update, mul_one, mul_zero]
      have hy : symp2fMul (p := 1) α₂ (symp2d (p := 0) (MvPolynomial.X 1)) = (0, α₂) := by
        simp [symp2fMul, symp2d, MvPolynomial.pderiv_X, Pi.single, Function.update, mul_one, mul_zero]
      have heq : (α₁, α₂) = symp2fMul (p := 1) α₁ (symp2d (p := 0) (MvPolynomial.X 0)) +
                             symp2fMul (p := 1) α₂ (symp2d (p := 0) (MvPolynomial.X 1)) := by
        rw [hx, hy]; simp [Prod.mk_add_mk]
      rw [heq, hT_add]
      simp [hT_gen]
    | 1 =>


      intro h
      have hgen : symp2d (p := 1) ((0 : Poly2), MvPolynomial.X (0 : Fin 2)) = (1 : Poly2) := by
        simp [symp2d, MvPolynomial.pderiv_X, Pi.single, Function.update, map_zero]
      have hmul : symp2fMul (p := 2) h (1 : Poly2) = h := by
        simp [symp2fMul, mul_one]
      have heq : h = symp2fMul (p := 2) h (symp2d (p := 1) ((0 : Poly2), MvPolynomial.X (0 : Fin 2))) := by
        rw [hgen, hmul]
      rw [heq]
      exact hT_gen h ((0 : Poly2), MvPolynomial.X (0 : Fin 2))
    | _ + 2 =>

      intro β
      exact Subsingleton.elim _ _


  ι_one_form_nondegenerate := by
    intro ⟨f, g⟩ h


    have h1 := h (1, 0)
    have h2 := h (0, 1)
    simp [symp2Iota] at h1 h2
    exact Prod.ext h1 h2


  ι_two_form_nondegenerate := by
    intro ω h


    have h1 := h (1, 0)
    simp [symp2Iota] at h1
    exact h1


end
