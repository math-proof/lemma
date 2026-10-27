import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc84b_grahamsospositiv.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc84b_parity_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_parity_closed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset (Fin 4)}
-- given
  (hA : A = ∅ ∨ A = Finset.univ)
  (hB : B = ∅ ∨ B = Finset.univ) :
-- imply
  A ∆ B = ∅ ∨ A ∆ B = Finset.univ := by
-- proof
  apply StatMech.Walls.gc84b_parity_closed G A B hA hB

/--
[gc84b_parityCorr_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_parityCorr_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Fin 4)}
-- given
  (h : S ≠ ∅ ∧ S ≠ Finset.univ) :
-- imply
  gc84b_parityCorr S = 0 := by
-- proof
  apply StatMech.Walls.gc84b_parityCorr_zero G S h

/--
[gc84b_parity_gks1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_parity_gks1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Fin 4)} :
-- imply
  0 ≤ gc84b_parityCorr S := by
-- proof
  apply StatMech.Walls.gc84b_parity_gks1 G S

/--
[gc84b_parity_gks2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_parity_gks2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset (Fin 4)} :
-- imply
  gc84b_parityCorr A * gc84b_parityCorr B ≤ gc84b_parityCorr (A ∆ B) := by
-- proof
  apply StatMech.Walls.gc84b_parity_gks2 G A B

/--
[gc84b_parity_griffiths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_parity_griffiths_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  gc84b_GriffithsFamily gc84b_parityCorr := by
-- proof
  apply StatMech.Walls.gc84b_parity_griffiths G

/--
[gc84b_parity_violates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_parity_violates_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  gc84b_ghsResidual gc84b_parityCorr < 0 := by
-- proof
  apply StatMech.Walls.gc84b_parity_violates G

/--
[gc84b_nonneg_combination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_nonneg_combination_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : Finset ι}
  {lam : ι → ℝ}
  {gen : ι → ℝ}
-- given
  (hlam : ∀ i ∈ s, 0 ≤ lam i)
  (hgen : ∀ i ∈ s, 0 ≤ gen i) :
-- imply
  0 ≤ ∑ i ∈ s, lam i * gen i := by
-- proof
  apply StatMech.Walls.gc84b_nonneg_combination G s lam gen hlam hgen

/--
[gc84b_no_positivstellensatz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_no_positivstellensatz_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ¬ gc84b_GriffithsConsequence gc84b_ghsResidual := by
-- proof
  apply StatMech.Walls.gc84b_no_positivstellensatz G

/--
[gc84b_griffithsFamily_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_griffithsFamily_insufficient_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ c : Finset (Fin 4) → ℝ, gc84b_GriffithsFamily c ∧ ¬ (0 ≤ gc84b_ghsResidual c) := by
-- proof
  apply StatMech.Walls.gc84b_griffithsFamily_insufficient G

/--
[gc84b_griffiths_sound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_griffiths_sound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, some y} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some y, none} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ∧ (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some y} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some x, none} ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) {some o, some x, some y, none} * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) := by
-- proof
  apply StatMech.Walls.gc84b_griffiths_sound G β h hβ hh o x y hox hoy hxy

/--
[gc84b_residual_closes_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_residual_closes_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hpoly : gc27_GHSPolyIneq G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc84b_residual_closes_ghs G β h o x y hox hoy hxy hpoly

/--
[gc84b_directSOS_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean)
-/
@[path]
private lemma gc84b_directSOS_status_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  (gc84b_GriffithsFamily gc84b_parityCorr ∧ gc84b_ghsResidual gc84b_parityCorr < 0) ∧ ¬ gc84b_GriffithsConsequence gc84b_ghsResidual ∧ (∃ c : Finset (Fin 4) → ℝ, gc84b_GriffithsFamily c ∧ ¬ (0 ≤ gc84b_ghsResidual c)) := by
-- proof
  apply StatMech.Walls.gc84b_directSOS_status G


-- created on 2026-10-23
