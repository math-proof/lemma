/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Def.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Sharpness

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]


section Isolated

variable {X Y : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]

theorem wJ_sym2FinsetInl_isolated
    (E : Finset (Sym2 X)) (J : Sym2 (X ⊕ Y) → ℝ)
    (s : ConfigSpace X) (t : ConfigSpace Y) :
    wJ (sym2FinsetInl E) J (fun _ => 0)
        (isingSumConfigEquiv.symm (s, t)) =
      wJ E (fun e => J (Sym2.map Sum.inl e)) (fun _ => 0) s := by
  unfold wJ sym2FinsetInl
  congr 1
  rw [Finset.sum_image]
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro e he
      rw [bond_isingSumConfigEquiv_symm_inl]
    · simp
  · intro a _ b _ hab
    exact Sym2.map.injective Sum.inl_injective hab

theorem sum_wJ_sym2FinsetInl
    (E : Finset (Sym2 X)) (J : Sym2 (X ⊕ Y) → ℝ) :
    (∑ omega : ConfigSpace (X ⊕ Y),
      wJ (sym2FinsetInl E) J (fun _ => 0) omega) =
      (Fintype.card (ConfigSpace Y) : ℝ) *
        ∑ s : ConfigSpace X,
          wJ E (fun e => J (Sym2.map Sum.inl e)) (fun _ => 0) s := by
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [wJ_sym2FinsetInl_isolated E J]
  calc
    (∑ s : ConfigSpace X, ∑ _t : ConfigSpace Y,
        wJ E (fun e => J (Sym2.map Sum.inl e)) (fun _ => 0) s) =
      ∑ s : ConfigSpace X, (Fintype.card (ConfigSpace Y) : ℝ) *
        wJ E (fun e => J (Sym2.map Sum.inl e)) (fun _ => 0) s := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by rw [Finset.mul_sum]

theorem sum_spinProd_wJ_sym2FinsetInl
    (E : Finset (Sym2 X)) (J : Sym2 (X ⊕ Y) → ℝ)
    (A : Finset X) :
    (∑ omega : ConfigSpace (X ⊕ Y),
      spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩) omega *
        wJ (sym2FinsetInl E) J (fun _ => 0) omega) =
      (Fintype.card (ConfigSpace Y) : ℝ) *
        ∑ s : ConfigSpace X,
          spinProd A s *
            wJ E (fun e => J (Sym2.map Sum.inl e)) (fun _ => 0) s := by
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  have hspin (s : ConfigSpace X) (t : ConfigSpace Y) :
      spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)
          (isingSumConfigEquiv.symm (s, t)) = spinProd A s := by
    unfold spinProd
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro x hx
    rfl
  simp_rw [hspin, wJ_sym2FinsetInl_isolated E J]
  calc
    (∑ s : ConfigSpace X, ∑ _t : ConfigSpace Y,
        spinProd A s *
          wJ E (fun e => J (Sym2.map Sum.inl e)) (fun _ => 0) s) =
      ∑ s : ConfigSpace X, (Fintype.card (ConfigSpace Y) : ℝ) *
        (spinProd A s *
          wJ E (fun e => J (Sym2.map Sum.inl e)) (fun _ => 0) s) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := by rw [Finset.mul_sum]


theorem expJ_spinProd_sym2FinsetInl_isolated
    (E : Finset (Sym2 X)) (J : Sym2 (X ⊕ Y) → ℝ)
    (A : Finset X) :
    expJ (sym2FinsetInl E) J (fun _ => 0)
        (spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) =
      expJ E (fun e => J (Sym2.map Sum.inl e)) (fun _ => 0)
        (spinProd A) := by
  unfold expJ ZJ
  rw [sum_spinProd_wJ_sym2FinsetInl E J A,
    sum_wJ_sym2FinsetInl E J]
  have hc : (Fintype.card (ConfigSpace Y) : ℝ) ≠ 0 := by positivity
  field_simp [hc]

end Isolated

section Domain

variable {U : Type*} [Fintype U] [DecidableEq U]


theorem expJ_spinProd_induce_le
    (P : U → Prop) [DecidablePred P]
    (E : Finset (Sym2 {x // P x})) (F : Finset (Sym2 U))
    (J : Sym2 U → ℝ)
    (hsub : sym2FinsetImage (StatMech.FK.agl_sumEquiv P)
        (sym2FinsetInl (Y := {x // ¬P x}) E) ⊆ F)
    (hJ : ∀ e ∈ F, 0 ≤ J e)
    (hdiag : ∀ e ∈ F, ¬e.IsDiag)
    (A : Finset {x // P x}) :
    expJ E (fun e => J (Sym2.map Subtype.val e)) (fun _ => 0)
        (spinProd A) ≤
      expJ F J (fun _ => 0)
        (spinProd (A.map (Function.Embedding.subtype P))) := by
  let sigma := StatMech.FK.agl_sumEquiv P
  let E' : Finset (Sym2 ({x // P x} ⊕ {x // ¬P x})) :=
    sym2FinsetInl E
  let J' : Sym2 ({x // P x} ⊕ {x // ¬P x}) → ℝ :=
    fun e => J (Sym2.map sigma e)
  have hsmall :
      expJ E (fun e => J (Sym2.map Subtype.val e)) (fun _ => 0)
          (spinProd A) =
        expJ (sym2FinsetImage sigma E') J (fun _ => 0)
          (spinProd ((A.map ⟨Sum.inl, Sum.inl_injective⟩).map
            sigma.toEmbedding)) := by
    calc
      _ = expJ E (fun e => J' (Sym2.map Sum.inl e)) (fun _ => 0)
          (spinProd A) := by
            congr 2
            funext e
            induction e using Sym2.inductionOn with
            | _ x y => simp [J', sigma, Sym2.map_pair_eq]
      _ = expJ E' J' (fun _ => 0)
          (spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) :=
            (expJ_spinProd_sym2FinsetInl_isolated E J' A).symm
      _ = _ := expJ_spinProd_sym2FinsetImage_relabel sigma E' J
        (fun _ => 0) (A.map ⟨Sum.inl, Sum.inl_injective⟩)
  rw [hsmall]
  have hmono := griffiths_mono
    (sym2FinsetImage sigma E') F J (fun _ => 0) hsub hJ
      (fun _ => le_rfl) (fun e he _ => hdiag e he)
      ((A.map ⟨Sum.inl, Sum.inl_injective⟩).map sigma.toEmbedding)
  have hmap :
      (A.map ⟨Sum.inl, Sum.inl_injective⟩).map sigma.toEmbedding =
        A.map (Function.Embedding.subtype P) := by
    rw [Finset.map_map]
    apply congrArg (fun f : {x // P x} ↪ U => A.map f)
    ext x
    rfl
  simpa only [hmap] using hmono

end Domain
end StatMech.FrontierB
