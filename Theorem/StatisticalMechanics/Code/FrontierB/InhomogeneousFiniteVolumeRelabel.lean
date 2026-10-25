/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Def.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel
open scoped BigOperators
open Finset


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Sharpness

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]


theorem sum_edgeCoupling_bond_relabel
    (sigma : V ≃ W) (E : Finset (Sym2 V))
    (J : Sym2 W → ℝ) (omega : ConfigSpace W) :
    (∑ e ∈ E, J (Sym2.map sigma e) *
        bond (isingCfgEquiv sigma omega) e) =
      ∑ f ∈ sym2FinsetImage sigma E, J f * bond omega f := by
  unfold sym2FinsetImage
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e he
    rw [bond_isingCfgEquiv]
  · intro a _ b _ hab
    exact Sym2.map.injective sigma.injective hab

theorem wJ_sym2FinsetImage_relabel
    (sigma : V ≃ W) (E : Finset (Sym2 V))
    (J : Sym2 W → ℝ) (hf : W → ℝ) (omega : ConfigSpace W) :
    wJ E (fun e => J (Sym2.map sigma e)) (fun x => hf (sigma x))
        (isingCfgEquiv sigma omega) =
      wJ (sym2FinsetImage sigma E) J hf omega := by
  unfold wJ
  congr 1
  rw [sum_edgeCoupling_bond_relabel sigma E J omega]
  rw [StatMech.Ising.ghsi_fieldSum_relabel sigma
    (fun x => hf (sigma x)) hf (fun _ => rfl) omega]

theorem ZJ_sym2FinsetImage_relabel
    (sigma : V ≃ W) (E : Finset (Sym2 V))
    (J : Sym2 W → ℝ) (hf : W → ℝ) :
    ZJ E (fun e => J (Sym2.map sigma e)) (fun x => hf (sigma x)) =
      ZJ (sym2FinsetImage sigma E) J hf := by
  unfold ZJ
  rw [← Equiv.sum_comp (isingCfgEquiv sigma)
    (fun omega => wJ E (fun e => J (Sym2.map sigma e))
      (fun x => hf (sigma x)) omega)]
  apply Finset.sum_congr rfl
  intro omega _
  exact wJ_sym2FinsetImage_relabel sigma E J hf omega

theorem spinProd_isingCfgEquiv
    (sigma : V ≃ W) (A : Finset V) (omega : ConfigSpace W) :
    spinProd A (isingCfgEquiv sigma omega) =
      spinProd (A.map sigma.toEmbedding) omega := by
  unfold spinProd
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro x hx
  rfl


theorem expJ_spinProd_sym2FinsetImage_relabel
    (sigma : V ≃ W) (E : Finset (Sym2 V))
    (J : Sym2 W → ℝ) (hf : W → ℝ) (A : Finset V) :
    expJ E (fun e => J (Sym2.map sigma e)) (fun x => hf (sigma x))
        (spinProd A) =
      expJ (sym2FinsetImage sigma E) J hf
        (spinProd (A.map sigma.toEmbedding)) := by
  unfold expJ
  rw [ZJ_sym2FinsetImage_relabel sigma E J hf]
  rw [← Equiv.sum_comp (isingCfgEquiv sigma)
    (fun omega => spinProd A omega *
      wJ E (fun e => J (Sym2.map sigma e))
        (fun x => hf (sigma x)) omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro omega _
  rw [spinProd_isingCfgEquiv,
    wJ_sym2FinsetImage_relabel sigma E J hf omega]

end StatMech.FrontierB
