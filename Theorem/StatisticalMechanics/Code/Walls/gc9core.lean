/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc8core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc9Znormaliserpos
import Theorem.StatisticalMechanics.Code.Walls.gc9assembledDnonneg.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc9deltadef
import Theorem.StatisticalMechanics.Code.Walls.gc9Jnonneg
import Theorem.StatisticalMechanics.Code.Walls.gc9betaderivcov3
import Theorem.StatisticalMechanics.Code.Walls.gc9switching
import Theorem.StatisticalMechanics.Code.Walls.gc9eq15insertion
import Theorem.StatisticalMechanics.Code.Walls.gc6_ghostgraph
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Def.StatisticalMechanics.Code.Walls.gc9core
open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FieldGhostDict

open StatMech.Sharpness.GhostCurrentRep

open StatMech.Sharpness.FluxEdgeCopy (sourcePairDisconnSum sourcePairDisconnSum_eq_edgecopy)

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc9_assembledD_pair_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (o g x y : V) (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m) :
    0 ≤ gc9_assembledD_pair ends F J o g x y :=
  mul_nonneg (hJ _) (gc9_concrete_delta_nonneg ends F hF o g x y)


theorem gc9_eq20_symmDiff (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        ∆ ({some o, none} : Finset (Option V))
      = (({x, y} : Finset V).map someEmb) := by
  ext z
  cases z with
  | none => simp [Finset.mem_symmDiff, someEmb]
  | some a =>
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_map, someEmb,
      Function.Embedding.coeFn_mk, Finset.mem_singleton, Option.some.injEq, reduceCtorEq,
      false_or, or_false]
    constructor
    · rintro (⟨⟨b, hb, hba⟩, hne⟩ | ⟨hcon, hneg⟩)
      · subst hba; rcases hb with rfl | rfl | rfl
        · exact absurd rfl hne
        · exact ⟨b, by simp, rfl⟩
        · exact ⟨b, by simp, rfl⟩
      · exact absurd ⟨a, Or.inl hcon, rfl⟩ hneg
    · rintro ⟨b, hb, hba⟩; subst hba; rcases hb with rfl | rfl
      · exact Or.inl ⟨⟨b, by simp, rfl⟩, fun h => hox h.symm⟩
      · exact Or.inl ⟨⟨b, by simp, rfl⟩, fun h => hoy h.symm⟩


theorem gc9_eq20_uv (o : V) :
    ({some o, none} : Finset (Option V))
      = insert (none : Option V) (({o} : Finset V).map someEmb) := by
  ext z; cases z with
  | none => simp [someEmb]
  | some a => simp [someEmb]


theorem gc9_eq20_card_oxy (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    Odd (({o, x, y} : Finset V).card) := by
  rw [Finset.card_insert_of_notMem (by simp [hox, hoy]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]; decide


theorem gc9_eq20_card_xy (x y : V) (hxy : x ≠ y) :
    Even (({x, y} : Finset V).card) := by
  rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]; decide


theorem gc9_cov3_spinProd_form (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    cov3sym G β h o s(x, y)
      = isingExpectation G β h (spinProd ({o, x, y} : Finset V))
        - isingExpectation G β h (spinProd ({x, y} : Finset V))
          * isingExpectation G β h (spinProd ({o} : Finset V)) := by
  rw [cov3sym_mk]
  have e3 : isingExpectation G β h (spinProd ({o, x, y} : Finset V))
      = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y)) := by
    congr 1; funext s; unfold spinProd
    rw [Finset.prod_insert (by simp [hox, hoy]), Finset.prod_insert (by simp [hxy]),
        Finset.prod_singleton]
  have e2 : isingExpectation G β h (spinProd ({x, y} : Finset V))
      = isingExpectation G β h (fun s => spin s x * spin s y) := by
    congr 1; funext s; unfold spinProd
    rw [Finset.prod_insert (by simp [hxy]), Finset.prod_singleton]
  have e1 : isingExpectation G β h (spinProd ({o} : Finset V))
      = isingExpectation G β h (fun s => spin s o) := by
    congr 1; funext s; unfold spinProd; rw [Finset.prod_singleton]
  rw [e3, e2, e1]; ring


theorem gc9_eq20_perBond_cov3 (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) * cov3sym G β h o s(x, y)
      = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none := by
  set Jc := ghostCoupling h β (fun _ => 1 : Sym2 V → ℝ) with hJc
  set GG := withGhost G with hGG
  set Z := currentSum GG β Jc ∅ with hZdef
  have hZne : Z ≠ 0 := ne_of_gt (gc9_sourceless_pos GG β Jc)
  have huv : (some o : Option V) ≠ none := by simp
  
  have hrep3 : isingExpectation G β h (spinProd ({o, x, y} : Finset V))
      = currentSum GG β Jc (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) / Z :=
    gc6_ghostGraph_currentRatio_odd G β h ({o, x, y} : Finset V) (gc9_eq20_card_oxy o x y hox hoy hxy)
  
  have hrep1 : isingExpectation G β h (spinProd ({x, y} : Finset V))
      = currentSum GG β Jc ((insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
            ∆ ({some o, none} : Finset (Option V))) / Z := by
    rw [gc9_eq20_symmDiff o x y hox hoy hxy]
    exact fgd_isingExpectation_eq_currentSum_ratio G β h ({x, y} : Finset V)
      (gc9_eq20_card_xy x y hxy)
  
  have hrep2 : isingExpectation G β h (spinProd ({o} : Finset V))
      = currentSum GG β Jc ({some o, none} : Finset (Option V)) / Z := by
    rw [gc9_eq20_uv o]
    exact gc6_ghostGraph_currentRatio_odd G β h ({o} : Finset V) (by simp)
  
  have hghost := gcr_ghostCurrentRep GG β Jc
      (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) huv
      Z (isingExpectation G β h (spinProd ({o, x, y} : Finset V)))
      (isingExpectation G β h (spinProd ({x, y} : Finset V)))
      (isingExpectation G β h (spinProd ({o} : Finset V)))
      hZdef hZne hrep3 hrep1 hrep2
  rw [gc9_cov3_spinProd_form G β h o x y hox hoy hxy]
  rw [show gc9_Z_normaliser G β Jc = Z ^ 2 from rfl]
  exact hghost


theorem gc9_ghostCoupling_nonneg (h β : ℝ) (hh : 0 ≤ h) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) :
    ∀ e, 0 ≤ ghostCoupling h β J e := by
  intro e
  induction e with
  | h a b =>
    cases a with
    | none =>
      cases b with
      | none => simp [ghostCoupling]
      | some y => simpa [ghostCoupling] using hh
    | some x =>
      cases b with
      | none => simpa [ghostCoupling] using hh
      | some y => rw [ghostCoupling_some_some]; exact hJ _


theorem gc9_disconnPivotal_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (A B : Finset (Option V)) (u v : Option V) :
    0 ≤ sourcePairDisconnSum (withGhost G) β (ghostCoupling h β J) A B u v := by
  rw [sourcePairDisconnSum_eq_edgecopy]
  refine tsum_nonneg (fun m => mul_nonneg (Finset.sum_nonneg (fun S _ => ?_)) ?_)
  · refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> · split <;> norm_num
  · exact acw_weight_nonneg (withGhost G) β (ghostCoupling h β J) hβ
      (gc9_ghostCoupling_nonneg h β hh J hJ) _


theorem gc9_eq20_pivotalMass_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none :=
  gc9_disconnPivotal_nonneg G β h hβ hh (fun _ => 1) (fun _ => by norm_num) _ _ _ _


theorem gc9_cov3_nonneg_of_eq20 (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    0 ≤ cov3sym G β h o s(x, y) := by
  have hid := gc9_eq20_perBond_cov3 G β h o x y hox hoy hxy
  have hZ : 0 < gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) :=
    gc9_Z_normaliser_pos G β (ghostCoupling h β (fun _ => 1))
  have hδ : 0 ≤ sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none :=
    gc9_eq20_pivotalMass_nonneg G β h hβ hh o x y
  
  nlinarith [hid, hZ, hδ]


end StatMech.Walls
