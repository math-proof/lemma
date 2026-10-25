/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PolynomialDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Theorem.v1.Atlas.GeometryOfManifolds.code.PolynomialDFS
set_option autoImplicit false


/-- Polynomial forms on $\mathbb{R}$ assemble into a `DifferentialFormSpace`, providing a
testbed scaffolding for de Rham cohomology in dimension $1$. -/
noncomputable instance polyDFS : DifferentialFormSpace PolyΩ PolyVF where
  instAddCommGroup := polyΩ_acg
  instModule := polyΩ_mod

  fMul := polyFMul
  wedge1 := polyWedge1
  d := polyD
  ι := fun X => polyIota X
  L := fun X => polyLie X


  d_add := by
    intro p α β
    match p with
    | 0 => exact Polynomial.derivative_add
    | _ + 1 => rfl


  d_smul := by
    intro p r α
    match p with
    | 0 => exact Polynomial.derivative_smul r α
    | _ + 1 => rfl


  d_squared := by
    intro p α
    match p with
    | 0 => rfl
    | _ + 1 => rfl


  d_fMul := by
    intro p f α
    match p with
    | 0 =>
      simp only [polyFMul, polyD, polyWedge1]
      exact Polynomial.derivative_mul
    | 1 => rfl
    | _ + 2 => rfl


  fMul_add_left := by
    intro p f g α
    match p with
    | 0 => simp only [polyFMul]; exact add_mul f g α
    | 1 => simp only [polyFMul]; exact add_mul f g α
    | _ + 2 => rfl


  fMul_add_right := by
    intro p f α β
    match p with
    | 0 => simp only [polyFMul]; exact mul_add f α β
    | 1 => simp only [polyFMul]; exact mul_add f α β
    | _ + 2 => rfl


  fMul_smul := by
    intro p r f α
    match p with
    | 0 => simp only [polyFMul]; exact smul_mul_assoc r f α
    | 1 => simp only [polyFMul]; exact smul_mul_assoc r f α
    | _ + 2 => rfl


  wedge1_add_right := by
    intro p ω α β
    match p with
    | 0 => simp only [polyWedge1]; exact mul_add ω α β
    | _ + 1 => rfl


  wedge1_smul_right := by
    intro p ω r α
    match p with
    | 0 => simp only [polyWedge1]; exact mul_smul_comm r ω α
    | _ + 1 => rfl


  ι_add := by
    intro X p α β
    match p with
    | 0 => simp only [polyIota]; exact mul_add X α β
    | 1 => simp only [polyIota]; ring
    | _ + 2 => rfl


  ι_smul := by
    intro X p r α
    match p with
    | 0 => simp only [polyIota]; exact mul_smul_comm r X α
    | 1 => simp only [polyIota]; simp [smul_zero]
    | _ + 2 => rfl


  ι_fMul := by
    intro X p f α
    match p with
    | 0 =>
      simp only [polyIota, polyFMul]
      ring
    | 1 =>
      simp only [polyIota, polyFMul]
      ring
    | _ + 2 => rfl


  ι_wedge1 := by
    intro X p ω α
    match p with
    | 0 =>
      simp only [polyIota, polyWedge1, polyFMul]
      ring
    | _ + 1 => rfl


  ι_squared := by
    intro X p α
    match p with
    | 0 =>
      simp only [polyIota]
      ring
    | 1 =>
      simp only [polyIota]
    | _ + 2 =>
      simp only [polyIota]


  ι_ι_anticomm := by
    intro X Y p α
    match p with
    | 0 =>
      simp only [polyIota]
      ring
    | 1 =>
      simp only [polyIota]
      simp [neg_zero]
    | _ + 2 =>
      simp only [polyIota]


  L_add := by
    intro X p α β
    match p with
    | 0 =>
      simp only [polyLie]
      rw [Polynomial.derivative_add, mul_add]
    | 1 =>
      simp only [polyLie]
      rw [mul_add, Polynomial.derivative_add]
    | _ + 2 => rfl


  L_smul := by
    intro X p r α
    match p with
    | 0 =>
      simp only [polyLie]
      rw [Polynomial.derivative_smul, mul_smul_comm]
    | 1 =>
      simp only [polyLie]
      rw [mul_smul_comm, Polynomial.derivative_smul]
    | _ + 2 => rfl


  L_zero_eq_ι_d := by
    intro X f
    simp only [polyLie, polyD, polyIota]


  L_comm_d := by
    intro X p α
    match p with
    | 0 =>
      simp only [polyLie, polyD]
    | _ + 1 => rfl


  L_fMul := by
    intro X p f α
    match p with
    | 0 =>
      simp only [polyLie, polyFMul]
      simp only [Polynomial.derivative_mul]; ring
    | 1 =>
      simp only [polyLie, polyFMul]
      simp only [Polynomial.derivative_mul]; ring
    | _ + 2 => rfl


  ext_fdα := by
    intro p T h_add h_smul h_gen
    match p with
    | 0 =>


      intro β
      have h1 : ∀ α : PolyΩ 0, T (polyFMul (1 : PolyΩ 0) (polyD α)) = 0 :=
        fun α => h_gen 1 α
      have h2 : ∀ α : PolyΩ 0, T (polyD α) = 0 := by
        intro α
        have := h1 α
        simp only [polyFMul, polyD] at this ⊢
        simpa using this
      rw [show β = Polynomial.derivative (polyAntideriv β) from (derivative_antideriv β).symm]
      exact h2 (polyAntideriv β)
    | _ + 1 =>

      intro β
      exact Subsingleton.elim _ _


  ι_one_form_nondegenerate := by
    intro α h


    have h1 := h (1 : PolyVF)
    simp only [polyIota] at h1
    simpa using h1


  ι_two_form_nondegenerate := by
    intro ω _
    exact Subsingleton.elim _ _

