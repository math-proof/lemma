/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Theorem.v1.Atlas.AlgebraicTopologyI.code.MayerVietoris
open Set Topology EilenbergSteenrod Function

universe u


namespace MayerVietoris

attribute [instance] MayerVietorisCover.instTop

/-- The Mayer-Vietoris long exact sequence (Theorem 11.5): from any Eilenberg-Steenrod
homology theory `h` and a cover `c = {A, B}` of `X` by sets whose interiors cover, we
construct the connecting homomorphism `∂` and the three exactness statements assembling
into the long exact sequence
`⋯ → H_n(A ∩ B) → H_n(A) ⊕ H_n(B) → H_n(X) → H_{n-1}(A ∩ B) → ⋯`. The proof factors
the boundary `H_{n+1}(X) → H_n(A ∩ B)` through the long exact sequence of the pair
`(X, A)` and the excised pair, using the homotopy equivalences `trSub`, `trSp`. -/
noncomputable def mayer_vietoris_sequence
    (h : HomologyTheory) (c : MayerVietorisCover) :
    MayerVietorisSequence h c := by
  let EP := c.EP
  have exc_bij : ∀ n, Bijective (h.map n (excisionInclusion c.pairXA c.Bᶜ)) :=
    fun n => h.excision n c.pairXA c.Bᶜ c.excisive
  let excEquiv (n : ℤ) : h.H n EP ≃+ h.H n c.pairXA :=
    AddEquiv.ofBijective (h.map n (excisionInclusion c.pairXA c.Bᶜ)) (exc_bij n)
  have trSub_bij (n : ℤ) : Bijective (h.map n c.trSub) :=
    transfer_bijective h n c.trSub c.trSubInv c.trSub_comp_inv_htpy c.trSubInv_comp_htpy
  have trSp_bij (n : ℤ) : Bijective (h.map n c.trSp) :=
    transfer_bijective h n c.trSp c.trSpInv c.trSp_comp_inv_htpy c.trSpInv_comp_htpy

  have trSub_inv : ∀ n x, (h.map n c.trSub) ((h.map n c.trSubInv) x) = x :=
    fun n => hom_inv_id h n c.trSubInv c.trSub c.trSub_comp_inv_htpy
  have trSubInv_inv : ∀ n x, (h.map n c.trSubInv) ((h.map n c.trSub) x) = x :=
    fun n => hom_inv_id h n c.trSub c.trSubInv c.trSubInv_comp_htpy
  have trSp_inv : ∀ n x, (h.map n c.trSp) ((h.map n c.trSpInv) x) = x :=
    fun n => hom_inv_id h n c.trSpInv c.trSp c.trSp_comp_inv_htpy
  have trSpInv_inv : ∀ n x, (h.map n c.trSpInv) ((h.map n c.trSp) x) = x :=
    fun n => hom_inv_id h n c.trSp c.trSpInv c.trSpInv_comp_htpy

  let conn (n : ℤ) : h.H (n + 1) c.pairX →+ h.H n c.pairAB :=
    (h.map n c.trSub).comp ((h.boundary n EP).comp ((excEquiv (n + 1)).symm.toAddMonoidHom.comp
      (h.map (n + 1) (inclusionSpaceToPair c.pairXA))))

  let j' (n : ℤ) : h.H n c.pairB →+ h.H n EP :=
    (h.map n (inclusionSpaceToPair EP)).comp (h.map n c.trSpInv)
  let d'prev (n : ℤ) : h.H (n + 1) EP →+ h.H n c.pairAB :=
    (h.map n c.trSub).comp (h.boundary n EP)

  have comm_kh : ∀ n x, h.map n c.inclA_X (h.map n c.inclAB_A x) =
      h.map n c.inclB_X (h.map n c.inclAB_B x) := by
    intro n x
    have := congr_arg (fun f => (h.map n f) x) c.inclA_X_comp_inclAB_A_eq
    simp only [h.map_comp] at this; exact this
  have comm_jf : ∀ n x, h.map n (inclusionSpaceToPair c.pairXA) (h.map n c.inclB_X x) =
      (excEquiv n) (j' n x) := by
    intro n x
    have := congr_arg (fun f => (h.map n f) x) c.comm2_eq
    simp only [h.map_comp] at this
    simp only [AddMonoidHom.comp_apply] at this; exact this
  have comm_dg : ∀ n x, h.boundary n c.pairXA ((excEquiv (n + 1)) x) =
      h.map n c.inclAB_A (d'prev n x) := by
    intro n x
    show h.boundary n c.pairXA (h.map (n + 1) (excisionInclusion c.pairXA c.Bᶜ) x) =
      h.map n c.inclAB_A ((h.map n c.trSub) (h.boundary n EP x))
    have nat := h.boundary_natural n (excisionInclusion c.pairXA c.Bᶜ)
    have := congr_fun (congr_arg DFunLike.coe nat) x
    simp only [AddMonoidHom.comp_apply] at this
    rw [← this, c.exc_restrictToSub_eq]
    have mc := h.map_comp n c.trSub c.inclAB_A
    exact congr_fun (congr_arg DFunLike.coe mc) ((h.boundary n EP) x)


  have inclAB_B_decomp : ∀ n y,
      (h.map n c.inclAB_B) y =
      (h.map n c.trSp) ((h.map n (inclusionSubToSpace EP)) ((h.map n c.trSubInv) y)) := by
    intro n y
    have := congr_arg (fun f => (h.map n f) y) c.inclAB_B_comp_eq.symm
    simp only [h.map_comp, AddMonoidHom.comp_apply] at this; exact this
  have bot_exact_sub : ∀ n, Exact (d'prev n) (h.map n c.inclAB_B) := by
    intro n y
    rw [inclAB_B_decomp]
    have he := exact_transfer_bij (h.exact_at_sub n EP)
      (h.map n c.trSub) (h.map n c.trSubInv) (trSub_inv n) (trSubInv_inv n)
      (h.map n c.trSp) (trSp_bij n).1
    exact he y
  have bot_exact_sp : ∀ n, Exact (h.map n c.inclAB_B) (j' n) := by
    intro n y
    constructor
    ·
      intro hy


      have hsp : (h.map n (inclusionSpaceToPair EP)) ((h.map n c.trSpInv) y) = 0 := hy
      obtain ⟨z, hz⟩ := (h.exact_at_space n EP ((h.map n c.trSpInv) y)).mp hsp


      refine ⟨(h.map n c.trSub) z, ?_⟩
      rw [inclAB_B_decomp, trSubInv_inv, hz, trSp_inv]
    ·
      rintro ⟨x, rfl⟩
      show (h.map n (inclusionSpaceToPair EP)) ((h.map n c.trSpInv) ((h.map n c.inclAB_B) x)) = 0
      rw [inclAB_B_decomp, trSpInv_inv n ((h.map n (inclusionSubToSpace EP)) _)]
      exact (h.exact_at_space n EP _).mpr ⟨(h.map n c.trSubInv) x, rfl⟩
  have bot_exact_pair : ∀ n, Exact (j' (n + 1)) (d'prev n) := by
    intro n y
    constructor
    ·
      intro hy

      have hbd : (h.boundary n EP) y = 0 := (trSub_bij n).1 (by rw [map_zero]; exact hy)

      obtain ⟨z, hz⟩ := (h.exact_at_pair n EP y).mp hbd


      exact ⟨(h.map (n + 1) c.trSp) z, by show (h.map (n+1) (inclusionSpaceToPair EP)) ((h.map (n+1) c.trSpInv) ((h.map (n+1) c.trSp) z)) = y; rw [trSpInv_inv, hz]⟩
    ·
      rintro ⟨x, rfl⟩
      show (h.map n c.trSub) ((h.boundary n EP) ((h.map (n + 1) (inclusionSpaceToPair EP)) ((h.map (n + 1) c.trSpInv) x))) = 0
      rw [(h.exact_at_pair n EP _).mpr ⟨(h.map (n + 1) c.trSpInv) x, rfl⟩, map_zero]
  refine ⟨conn, ?_, ?_, ?_⟩
  · intro n
    exact exact_at_prod (h.map n c.inclA_X) (h.map n (inclusionSpaceToPair c.pairXA))
      (h.map n c.inclAB_B) (j' n) (h.map n c.inclAB_A) (h.map n c.inclB_X) (excEquiv n)
      (h.boundary n c.pairXA) (d'prev n) (excEquiv (n + 1))
      (h.exact_at_space n c.pairXA) (bot_exact_sp n) (h.exact_at_sub n c.pairXA) (bot_exact_sub n)
      (comm_kh n) (fun x => comm_jf n x) (fun x => comm_dg n x)
  · intro n
    exact exact_at_A (h.map (n + 1) c.inclA_X) (h.map (n + 1) (inclusionSpaceToPair c.pairXA))
      (j' (n + 1)) (d'prev n) (h.map (n + 1) c.inclB_X) (excEquiv (n + 1))
      (h.exact_at_space (n + 1) c.pairXA) (bot_exact_pair n) (fun x => comm_jf (n + 1) x)
  · intro n
    exact exact_at_C' (h.map (n + 1) (inclusionSpaceToPair c.pairXA)) (h.boundary n c.pairXA)
      (h.map n c.inclAB_B) (d'prev n) (h.map n c.inclAB_A) (excEquiv (n + 1))
      (h.exact_at_pair n c.pairXA) (bot_exact_sub n) (fun x => comm_dg n x)

end MayerVietoris
