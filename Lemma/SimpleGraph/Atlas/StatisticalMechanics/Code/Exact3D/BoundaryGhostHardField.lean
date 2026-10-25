import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
open Filter StatMech StatMech.Exact3D


/--
[boundaryGhostOnePointObservable_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostOnePointObservable_eq_eq
  {d n : ℕ}
  {σ : BoundaryGhostConfig d n} :
-- imply
  boundaryGhostOnePointObservable d n σ = Ising.spin σ (some (IsingFK.boxOrigin d n)) * Ising.spin σ none := by
-- proof
  apply StatMech.Exact3D.boundaryGhostOnePointObservable_eq d n σ

/--
[boundaryGhostMismatchCount_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostMismatchCount_eq_zero_iff_eq
  {d n : ℕ}
  {σ : BoundaryGhostConfig d n} :
-- imply
  boundaryGhostMismatchCount d n σ = 0 ↔ ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → σ (some x) = σ none := by
-- proof
  apply StatMech.Exact3D.boundaryGhostMismatchCount_eq_zero_iff d n σ

/--
[boundaryGhost_bond_some_none_eq_if](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhost_bond_some_none_eq_if_eq
  {σ : ConfigSpace (Option V)}
  {x : V} :
-- imply
  Ising.bond σ s(some x, none) = if σ (some x) = σ none then 1 else -1 := by
-- proof
  apply StatMech.Exact3D.boundaryGhost_bond_some_none_eq_if σ x

/--
[finset_sum_ite_neg_one_eq_card_sub_two_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finset_sum_ite_neg_one_eq_card_sub_two_filter_eq
  {s : Finset α}
  [DecidablePred p]
-- given
  (p : α → Prop) :
-- imply
  (∑ x ∈ s, if p x then (-1 : ℝ) else 1) = (s.card : ℝ) - 2 * ((s.filter p).card : ℝ) := by
-- proof
  apply StatMech.Exact3D.finset_sum_ite_neg_one_eq_card_sub_two_filter s p

/--
[boundaryGhost_boundaryBondSum_eq_card_sub_two_mismatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhost_boundaryBondSum_eq_card_sub_two_mismatch_eq
  {d n : ℕ}
  {σ : BoundaryGhostConfig d n} :
-- imply
  (∑ x ∈ (Finset.univ.filter (FK.boxBoundary d n)), Ising.bond σ s(some x, none)) = (((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ) - 2 * (boundaryGhostMismatchCount d n σ : ℝ)) := by
-- proof
  apply StatMech.Exact3D.boundaryGhost_boundaryBondSum_eq_card_sub_two_mismatch d n σ

/--
[boundaryGhost_weightedBondSum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhost_weightedBondSum_split_eq
  {d n : ℕ}
  {H : ℝ}
  {σ : BoundaryGhostConfig d n} :
-- imply
  (∑ e ∈ (Sharpness.withGhost (FK.boxGraph d n)).edgeFinset, boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1) e * Ising.bond σ e) = (∑ e ∈ (FK.boxGraph d n).edgeFinset, (1 : ℝ) * Ising.bond (fun x => σ (some x)) e) + H * ∑ x ∈ (Finset.univ.filter (FK.boxBoundary d n)), Ising.bond σ s(some x, none) := by
-- proof
  apply StatMech.Exact3D.boundaryGhost_weightedBondSum_split d n H σ

/--
[boundaryGhost_weightedBondSum_eq_original_add_mismatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhost_weightedBondSum_eq_original_add_mismatch_eq
  {d n : ℕ}
  {H : ℝ}
  {σ : BoundaryGhostConfig d n} :
-- imply
  (∑ e ∈ (Sharpness.withGhost (FK.boxGraph d n)).edgeFinset, boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1) e * Ising.bond σ e) = (∑ e ∈ (FK.boxGraph d n).edgeFinset, (1 : ℝ) * Ising.bond (fun x => σ (some x)) e) + H * (((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ) - 2 * (boundaryGhostMismatchCount d n σ : ℝ)) := by
-- proof
  apply StatMech.Exact3D.boundaryGhost_weightedBondSum_eq_original_add_mismatch d n H σ

/--
[boundaryGhost_boltzmannJ_eq_common_mul_base_mul_countFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhost_boltzmannJ_eq_common_mul_base_mul_countFactor_eq
  {d n : ℕ}
  {β H : ℝ}
  {σ : BoundaryGhostConfig d n} :
-- imply
  Sharpness.boltzmannJ (Sharpness.withGhost (FK.boxGraph d n)) β (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) σ = Real.exp (β * H * ((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ)) * boundaryGhostOriginalBase d n β σ * boundaryGhostCountFactor d n β H σ := by
-- proof
  apply StatMech.Exact3D.boundaryGhost_boltzmannJ_eq_common_mul_base_mul_countFactor d n β H σ

/--
[boundaryGhostCountFactor_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostCountFactor_tendsto_eq
  {d n : ℕ}
  {β : ℝ}
  {σ : BoundaryGhostConfig d n}
-- given
  (hβ : 0 < β) :
-- imply
  Tendsto (fun H : ℝ => boundaryGhostCountFactor d n β H σ) atTop (𝓝 (boundaryGhostAlignedLimitFactor d n σ)) := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCountFactor_tendsto d n hβ σ

/--
[boundaryGhostCountFactorRatio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostCountFactorRatio_tendsto_eq
  {d n : ℕ}
  {β : ℝ}
  {base obs : BoundaryGhostConfig d n → ℝ}
-- given
  (hβ : 0 < β)
  (hden : finiteFactorLimitDenominator (Finset.univ : Finset (BoundaryGhostConfig d n)) base (boundaryGhostAlignedLimitFactor d n) ≠ 0) :
-- imply
  Tendsto (fun H : ℝ => finiteFactorRatio (Finset.univ : Finset (BoundaryGhostConfig d n)) base obs (boundaryGhostCountFactor d n β) H) atTop (𝓝 (finiteFactorLimitRatio (Finset.univ : Finset (BoundaryGhostConfig d n)) base obs (boundaryGhostAlignedLimitFactor d n))) := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCountFactorRatio_tendsto d n hβ base obs hden

/--
[boundaryGhostExpectationJ_eq_countFactorRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostExpectationJ_eq_countFactorRatio_eq
  {d n : ℕ}
  {β H : ℝ} :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph d n)) β (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource d n) = finiteFactorRatio (Finset.univ : Finset (BoundaryGhostConfig d n)) (boundaryGhostOriginalBase d n β) (boundaryGhostOnePointObservable d n) (boundaryGhostCountFactor d n β) H := by
-- proof
  apply StatMech.Exact3D.boundaryGhostExpectationJ_eq_countFactorRatio d n β H

/--
[finiteBoundaryGhostCurrentOnePoint_eq_countFactorRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_eq_countFactorRatio_eq
  {d n : ℕ}
  {β H : ℝ} :
-- imply
  finiteBoundaryGhostCurrentOnePoint d n β H = finiteFactorRatio (Finset.univ : Finset (BoundaryGhostConfig d n)) (boundaryGhostOriginalBase d n β) (boundaryGhostOnePointObservable d n) (boundaryGhostCountFactor d n β) H := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCurrentOnePoint_eq_countFactorRatio d n β H

/--
[isingSpin_bToF_eq_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma isingSpin_bToF_eq_spin_eq
  {τ : ConfigSpace V}
  {x : V} :
-- imply
  FK.isingSpin (IsingFK.bToF (τ x)) = Ising.spin τ x := by
-- proof
  apply StatMech.Exact3D.isingSpin_bToF_eq_spin τ x

/--
[isingBond_bToF_eq_bond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma isingBond_bToF_eq_bond_eq
  {τ : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  IsingFK.isingBond (fun x => IsingFK.bToF (τ x)) e = Ising.bond τ e := by
-- proof
  apply StatMech.Exact3D.isingBond_bToF_eq_bond τ e

/--
[boltzmannJ_one_flipV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boltzmannJ_one_flipV_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {τ : ConfigSpace V} :
-- imply
  Sharpness.boltzmannJ G β (fun _ => 1) (Sharpness.FieldGhostDict.flipV τ) = Sharpness.boltzmannJ G β (fun _ => 1) τ := by
-- proof
  apply StatMech.Exact3D.boltzmannJ_one_flipV G β τ

/--
[isingWiredWeight_bToF_eq_if](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma isingWiredWeight_bToF_eq_if_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {β : ℝ}
  {τ : ConfigSpace V}
-- given
  (bdry : V → Prop) :
-- imply
  IsingFK.isingWiredWeight G bdry β (fun x => IsingFK.bToF (τ x)) = if (∀ x : V, bdry x → τ x = true) then Sharpness.boltzmannJ G β (fun _ => 1) τ else 0 := by
-- proof
  apply StatMech.Exact3D.isingWiredWeight_bToF_eq_if G bdry β τ

/--
[isingWiredZ_eq_boolBoundaryBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma isingWiredZ_eq_boolBoundaryBase_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {β : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  IsingFK.isingWiredZ G bdry β = ∑ τ : ConfigSpace V, if (∀ x : V, bdry x → τ x = true) then Sharpness.boltzmannJ G β (fun _ => 1) τ else 0 := by
-- proof
  apply StatMech.Exact3D.isingWiredZ_eq_boolBoundaryBase G bdry β

/--
[isingWiredOnePointNumerator_eq_boolBoundaryBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma isingWiredOnePointNumerator_eq_boolBoundaryBase_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {β : ℝ}
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  (∑ σ : V → Fin 2, IsingFK.isingWiredWeight G bdry β σ * FK.isingSpin (σ x)) = ∑ τ : ConfigSpace V, if (∀ y : V, bdry y → τ y = true) then Sharpness.boltzmannJ G β (fun _ => 1) τ * Ising.spin τ x else 0 := by
-- proof
  apply StatMech.Exact3D.isingWiredOnePointNumerator_eq_boolBoundaryBase G bdry β x

/--
[boundaryGhostMismatchCount_split_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostMismatchCount_split_eq_zero_iff_eq
  {d n : ℕ}
  {b : Bool}
  {τ : ConfigSpace (FK.boxVerts d n)} :
-- imply
  boundaryGhostMismatchCount d n (fun a => Option.rec b τ a : BoundaryGhostConfig d n) = 0 ↔ ∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = b := by
-- proof
  apply StatMech.Exact3D.boundaryGhostMismatchCount_split_eq_zero_iff d n b τ

/--
[boundaryGhostAlignedLimitFactor_split_eq_if](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostAlignedLimitFactor_split_eq_if_eq
  {d n : ℕ}
  {b : Bool}
  {τ : ConfigSpace (FK.boxVerts d n)} :
-- imply
  boundaryGhostAlignedLimitFactor d n (fun a => Option.rec b τ a : BoundaryGhostConfig d n) = if (∀ x : FK.boxVerts d n, FK.boxBoundary d n x → τ x = b) then 1 else 0 := by
-- proof
  apply StatMech.Exact3D.boundaryGhostAlignedLimitFactor_split_eq_if d n b τ

/--
[boundaryGhostOnePointObservable_split_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostOnePointObservable_split_true_eq
  {d n : ℕ}
  {τ : ConfigSpace (FK.boxVerts d n)} :
-- imply
  boundaryGhostOnePointObservable d n (fun a => Option.rec true τ a : BoundaryGhostConfig d n) = Ising.spin τ (IsingFK.boxOrigin d n) := by
-- proof
  apply StatMech.Exact3D.boundaryGhostOnePointObservable_split_true d n τ

/--
[boundaryGhostOnePointObservable_split_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostOnePointObservable_split_false_eq
  {d n : ℕ}
  {τ : ConfigSpace (FK.boxVerts d n)} :
-- imply
  boundaryGhostOnePointObservable d n (fun a => Option.rec false τ a : BoundaryGhostConfig d n) = -(Ising.spin τ (IsingFK.boxOrigin d n)) := by
-- proof
  apply StatMech.Exact3D.boundaryGhostOnePointObservable_split_false d n τ

/--
[boundaryGhostLimitDenominator_trueSector_eq_wiredZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostLimitDenominator_trueSector_eq_wiredZ_eq
  {d n : ℕ}
  {β : ℝ} :
-- imply
  (∑ τ : ConfigSpace (FK.boxVerts d n), boundaryGhostOriginalBase d n β (fun a => Option.rec true τ a : BoundaryGhostConfig d n) * boundaryGhostAlignedLimitFactor d n (fun a => Option.rec true τ a : BoundaryGhostConfig d n)) = IsingFK.isingWiredZ (FK.boxGraph d n) (FK.boxBoundary d n) β := by
-- proof
  apply StatMech.Exact3D.boundaryGhostLimitDenominator_trueSector_eq_wiredZ d n β

/--
[boundaryGhostLimitDenominator_falseSector_eq_wiredZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostLimitDenominator_falseSector_eq_wiredZ_eq
  {d n : ℕ}
  {β : ℝ} :
-- imply
  (∑ τ : ConfigSpace (FK.boxVerts d n), boundaryGhostOriginalBase d n β (fun a => Option.rec false τ a : BoundaryGhostConfig d n) * boundaryGhostAlignedLimitFactor d n (fun a => Option.rec false τ a : BoundaryGhostConfig d n)) = IsingFK.isingWiredZ (FK.boxGraph d n) (FK.boxBoundary d n) β := by
-- proof
  apply StatMech.Exact3D.boundaryGhostLimitDenominator_falseSector_eq_wiredZ d n β

/--
[boundaryGhostLimitDenominator_eq_two_mul_wiredZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostLimitDenominator_eq_two_mul_wiredZ_eq
  {d n : ℕ}
  {β : ℝ} :
-- imply
  finiteFactorLimitDenominator (Finset.univ : Finset (BoundaryGhostConfig d n)) (boundaryGhostOriginalBase d n β) (boundaryGhostAlignedLimitFactor d n) = 2 * IsingFK.isingWiredZ (FK.boxGraph d n) (FK.boxBoundary d n) β := by
-- proof
  apply StatMech.Exact3D.boundaryGhostLimitDenominator_eq_two_mul_wiredZ d n β

/--
[boundaryGhostLimitNumerator_trueSector_eq_wiredNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostLimitNumerator_trueSector_eq_wiredNumerator_eq
  {d n : ℕ}
  {β : ℝ} :
-- imply
  (∑ τ : ConfigSpace (FK.boxVerts d n), boundaryGhostOriginalBase d n β (fun a => Option.rec true τ a : BoundaryGhostConfig d n) * boundaryGhostAlignedLimitFactor d n (fun a => Option.rec true τ a : BoundaryGhostConfig d n) * boundaryGhostOnePointObservable d n (fun a => Option.rec true τ a : BoundaryGhostConfig d n)) = ∑ σ : FK.boxVerts d n → Fin 2, IsingFK.isingWiredWeight (FK.boxGraph d n) (FK.boxBoundary d n) β σ * FK.isingSpin (σ (IsingFK.boxOrigin d n)) := by
-- proof
  apply StatMech.Exact3D.boundaryGhostLimitNumerator_trueSector_eq_wiredNumerator d n β

/--
[boundaryGhostLimitNumerator_falseSector_eq_wiredNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostLimitNumerator_falseSector_eq_wiredNumerator_eq
  {d n : ℕ}
  {β : ℝ} :
-- imply
  (∑ τ : ConfigSpace (FK.boxVerts d n), boundaryGhostOriginalBase d n β (fun a => Option.rec false τ a : BoundaryGhostConfig d n) * boundaryGhostAlignedLimitFactor d n (fun a => Option.rec false τ a : BoundaryGhostConfig d n) * boundaryGhostOnePointObservable d n (fun a => Option.rec false τ a : BoundaryGhostConfig d n)) = ∑ σ : FK.boxVerts d n → Fin 2, IsingFK.isingWiredWeight (FK.boxGraph d n) (FK.boxBoundary d n) β σ * FK.isingSpin (σ (IsingFK.boxOrigin d n)) := by
-- proof
  apply StatMech.Exact3D.boundaryGhostLimitNumerator_falseSector_eq_wiredNumerator d n β

/--
[boundaryGhostLimitNumerator_eq_two_mul_wiredNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostLimitNumerator_eq_two_mul_wiredNumerator_eq
  {d n : ℕ}
  {β : ℝ} :
-- imply
  finiteFactorLimitNumerator (Finset.univ : Finset (BoundaryGhostConfig d n)) (boundaryGhostOriginalBase d n β) (boundaryGhostOnePointObservable d n) (boundaryGhostAlignedLimitFactor d n) = 2 * (∑ σ : FK.boxVerts d n → Fin 2, IsingFK.isingWiredWeight (FK.boxGraph d n) (FK.boxBoundary d n) β σ * FK.isingSpin (σ (IsingFK.boxOrigin d n))) := by
-- proof
  apply StatMech.Exact3D.boundaryGhostLimitNumerator_eq_two_mul_wiredNumerator d n β

/--
[boundaryGhostAlignedLimitRatio_eq_wiredOnePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostAlignedLimitRatio_eq_wiredOnePoint_eq
  {d n : ℕ}
  {β : ℝ} :
-- imply
  finiteFactorLimitRatio (Finset.univ : Finset (BoundaryGhostConfig d n)) (boundaryGhostOriginalBase d n β) (boundaryGhostOnePointObservable d n) (boundaryGhostAlignedLimitFactor d n) = IsingFK.isingWiredOnePoint (FK.boxGraph d n) (FK.boxBoundary d n) β (IsingFK.boxOrigin d n) := by
-- proof
  apply StatMech.Exact3D.boundaryGhostAlignedLimitRatio_eq_wiredOnePoint d n β

/--
[boundaryGhostOriginalBase_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostOriginalBase_pos_eq
  {d n : ℕ}
  {β : ℝ}
  {σ : BoundaryGhostConfig d n} :
-- imply
  0 < boundaryGhostOriginalBase d n β σ := by
-- proof
  apply StatMech.Exact3D.boundaryGhostOriginalBase_pos d n β σ

/--
[boundaryGhostAlignedLimitDenominator_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma boundaryGhostAlignedLimitDenominator_ne_zero_eq
  {d n : ℕ}
  {β : ℝ} :
-- imply
  finiteFactorLimitDenominator (Finset.univ : Finset (BoundaryGhostConfig d n)) (boundaryGhostOriginalBase d n β) (boundaryGhostAlignedLimitFactor d n) ≠ 0 := by
-- proof
  apply StatMech.Exact3D.boundaryGhostAlignedLimitDenominator_ne_zero d n β

/--
[finiteBoundaryGhostAlignedLimitIdentification_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteBoundaryGhostAlignedLimitIdentification_of_pos_eq
  {d n : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  FiniteBoundaryGhostAlignedLimitIdentification d n β where beta_pos := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostAlignedLimitIdentification_of_pos d n hβ

/--
[finiteBoundaryGhostCountFactorDictionary_of_alignedLimitIdentification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteBoundaryGhostCountFactorDictionary_of_alignedLimitIdentification_eq
  {d n : ℕ}
  {β : ℝ}
  {D : FiniteBoundaryGhostAlignedLimitIdentification d n β} :
-- imply
  FiniteBoundaryGhostCountFactorDictionary d n β (boundaryGhostOriginalBase d n β) (boundaryGhostOnePointObservable d n) where beta_pos := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCountFactorDictionary_of_alignedLimitIdentification D

/--
[finiteBoundaryGhostFactorDictionary_of_countFactorDictionary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteBoundaryGhostFactorDictionary_of_countFactorDictionary_eq
  {d n : ℕ}
  {β : ℝ}
  {base obs : BoundaryGhostConfig d n → ℝ}
  {D : FiniteBoundaryGhostCountFactorDictionary d n β base obs} :
-- imply
  FiniteBoundaryGhostFactorDictionary d n β base obs (boundaryGhostAlignedLimitFactor d n) (boundaryGhostCountFactor d n β) where current_eq := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostFactorDictionary_of_countFactorDictionary D

/--
[finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_factorDictionary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_factorDictionary_eq
  {d n : ℕ}
  {β : ℝ}
  {base obs limitFactor : BoundaryGhostConfig d n → ℝ}
  {factor : ℝ → BoundaryGhostConfig d n → ℝ}
  {D : FiniteBoundaryGhostFactorDictionary d n β base obs limitFactor factor} :
-- imply
  Tendsto (fun H : ℝ => finiteBoundaryGhostCurrentOnePoint d n β H) atTop (𝓝 (IsingFK.isingWiredOnePoint (FK.boxGraph d n) (FK.boxBoundary d n) β (IsingFK.boxOrigin d n))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_factorDictionary D

/--
[finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_countFactorDictionary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_countFactorDictionary_eq
  {d n : ℕ}
  {β : ℝ}
  {base obs : BoundaryGhostConfig d n → ℝ}
  {D : FiniteBoundaryGhostCountFactorDictionary d n β base obs} :
-- imply
  Tendsto (fun H : ℝ => finiteBoundaryGhostCurrentOnePoint d n β H) atTop (𝓝 (IsingFK.isingWiredOnePoint (FK.boxGraph d n) (FK.boxBoundary d n) β (IsingFK.boxOrigin d n))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_countFactorDictionary D

/--
[finiteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical_proved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical_proved_eq :
-- imply
  FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical_proved

/--
[finiteBoundaryGhostCountFactorDictionaryPositiveSubcritical_of_alignedLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteBoundaryGhostCountFactorDictionaryPositiveSubcritical_of_alignedLimit_eq
-- given
  (hdict : FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical) :
-- imply
  FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCountFactorDictionaryPositiveSubcritical_of_alignedLimit hdict

/--
[finiteBoundaryGhostFactorDictionaryPositiveSubcritical_of_countFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteBoundaryGhostFactorDictionaryPositiveSubcritical_of_countFactor_eq
-- given
  (hdict : FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical) :
-- imply
  FiniteBoundaryGhostFactorDictionaryPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostFactorDictionaryPositiveSubcritical_of_countFactor hdict

/--
[finiteQ2SimonBoundaryGhostHardFieldLimit_of_factorDictionary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostHardFieldLimit_of_factorDictionary_eq
-- given
  (hdict : FiniteBoundaryGhostFactorDictionaryPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteQ2SimonBoundaryGhostHardFieldLimit_of_factorDictionary hdict

/--
[finiteQ2SimonBoundaryGhostHardFieldLimit_of_countFactorDictionary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostHardFieldLimit_of_countFactorDictionary_eq
-- given
  (hdict : FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteQ2SimonBoundaryGhostHardFieldLimit_of_countFactorDictionary hdict

/--
[finiteQ2SimonBoundaryGhostHardFieldLimit_of_alignedLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostHardFieldLimit_of_alignedLimit_eq
-- given
  (hdict : FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteQ2SimonBoundaryGhostHardFieldLimit_of_alignedLimit hdict

/--
[finiteQ2SimonBoundaryGhostHardFieldLimit_from_exactAlignedSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostHardFieldLimit_from_exactAlignedSector_eq :
-- imply
  FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteQ2SimonBoundaryGhostHardFieldLimit_from_exactAlignedSector

/--
[finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector_eq :
-- imply
  FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector

/--
[finiteCurrentSimon_of_exactBoundaryGhostComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteCurrentSimon_of_exactBoundaryGhostComparison_eq
-- given
  (hcompare : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteCurrentSimon_of_exactBoundaryGhostComparison hcompare

/--
[finiteIsingSimon_of_exactBoundaryGhostComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteIsingSimon_of_exactBoundaryGhostComparison_eq
-- given
  (hcompare : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteIsingSimon_of_exactBoundaryGhostComparison hcompare

/--
[freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostComparison_eq
-- given
  (hcompare : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostComparison hcompare

/--
[freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison_eq
-- given
  (hcompare : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison hcompare

/--
[finiteCurrentSimon_of_exactBoundaryGhostFirstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteCurrentSimon_of_exactBoundaryGhostFirstExitPositive_eq
-- given
  (hfirst : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteCurrentSimon_of_exactBoundaryGhostFirstExitPositive hfirst

/--
[finiteIsingSimon_of_exactBoundaryGhostFirstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma finiteIsingSimon_of_exactBoundaryGhostFirstExitPositive_eq
-- given
  (hfirst : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteIsingSimon_of_exactBoundaryGhostFirstExitPositive hfirst

/--
[freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostFirstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostFirstExitPositive_eq
-- given
  (hfirst : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostFirstExitPositive hfirst

/--
[freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostFirstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostFirstExitPositive_eq
-- given
  (hfirst : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostFirstExitPositive hfirst


-- created on 2026-10-23
