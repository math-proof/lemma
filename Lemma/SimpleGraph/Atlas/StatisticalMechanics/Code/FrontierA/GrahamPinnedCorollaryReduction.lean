import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedCorollaryReduction.Part2
open Finset Classical StatMech StatMech.FrontierA


/--
[vbg_exp_grahamZeroProb_mul_spin_eq_zero_of_flipInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma vbg_exp_grahamZeroProb_mul_spin_eq_zero_of_flipInvariant_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (F : ConfigSpace V -> Real)
  (hF : forall s, F (FieldGhostDict.flipV s) = F s) :
-- imply
  vbg_exp (grahamZeroProb E J) (fun s => F s * spin s m) = 0 := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamZeroProb_mul_spin_eq_zero_of_flipInvariant E J m F hF

/--
[vbg_exp_grahamPinnedProb_eq_of_flipInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma vbg_exp_grahamPinnedProb_eq_of_flipInvariant_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (F : ConfigSpace V -> Real)
  (hF : forall s, F (FieldGhostDict.flipV s) = F s) :
-- imply
  vbg_exp (grahamPinnedProb E J m) F = expJ E J (fun _ => 0) F := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamPinnedProb_eq_of_flipInvariant E J m F hF

/--
[grahamAnchor_expJ_eq_zero_of_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamAnchor_expJ_eq_zero_of_invariant_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (F : ConfigSpace V -> Real)
  (hanchor : forall t, F (grahamPinConfig m t) = F t)
  (hflip : forall t, F (FieldGhostDict.flipV t) = F t) :
-- imply
  expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) F = expJ E J (fun _ => 0) F := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_expJ_eq_zero_of_invariant E J hdiag m F hanchor hflip

/--
[grahamAnchor_fourPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamAnchor_fourPoint_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (him : i ≠ m)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) (fun t => (spin t i * spin t j) * (spin t k * spin t l)) = grahamFourPoint E J i j k l := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_fourPoint_eq E J hdiag him hjm hkm hlm

/--
[grahamFieldFourPointLHS_anchor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamFieldFourPointLHS_anchor_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (him : i ≠ m)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  grahamFieldFourPointLHS E (grahamAnchorCoupling J m) (grahamAnchorField E J m) i j k l = grahamUrsell4 E J i j k l := by
-- proof
  apply StatMech.FrontierA.grahamFieldFourPointLHS_anchor_eq E J hdiag him hjm hkm hlm

/--
[grahamFieldFourPointRHS_anchor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamFieldFourPointRHS_anchor_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (him : i ≠ m)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  grahamFieldFourPointRHS E (grahamAnchorCoupling J m) (grahamAnchorField E J m) i j k l = grahamCorrectedRHS E J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamFieldFourPointRHS_anchor_eq E J hdiag him hjm hkm hlm

/--
[grahamCorrectedBound_iff_anchorField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamCorrectedBound_iff_anchorField_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (him : i ≠ m)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l m ↔ grahamFieldFourPointLHS E (grahamAnchorCoupling J m) (grahamAnchorField E J m) i j k l <= grahamFieldFourPointRHS E (grahamAnchorCoupling J m) (grahamAnchorField E J m) i j k l := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedBound_iff_anchorField E J hdiag him hjm hkm hlm

/--
[grahamUrsell4_pair_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamUrsell4_pair_rotate_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamUrsell4 E J i j k l = grahamUrsell4 E J k l i j := by
-- proof
  apply StatMech.FrontierA.grahamUrsell4_pair_rotate E J i j k l

/--
[grahamUrsell4_swap_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamUrsell4_swap_last_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamUrsell4 E J i j k l = grahamUrsell4 E J i j l k := by
-- proof
  apply StatMech.FrontierA.grahamUrsell4_swap_last E J i j k l

/--
[grahamUrsell4_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamUrsell4_cycle_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamUrsell4 E J i j k l = grahamUrsell4 E J j k l i := by
-- proof
  apply StatMech.FrontierA.grahamUrsell4_cycle E J i j k l

/--
[grahamCorrectedBound_aux_eq_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamCorrectedBound_aux_eq_first_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l i := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedBound_aux_eq_first E J hdiag hJ i j k l

/--
[grahamCorrectedBound_aux_eq_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamCorrectedBound_aux_eq_second_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l j := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedBound_aux_eq_second E J hdiag hJ i j k l

/--
[grahamCorrectedBound_aux_eq_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamCorrectedBound_aux_eq_third_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l k := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedBound_aux_eq_third E J hdiag hJ i j k l

/--
[grahamCorrectedBound_of_aux_mem_marks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedCorollaryReduction.lean)
-/
@[path]
private lemma grahamCorrectedBound_of_aux_mem_marks_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hJ : ∀ e, 0 <= J e)
  (hm : m = i ∨ m = j ∨ m = k ∨ m = l) :
-- imply
  grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedBound_of_aux_mem_marks E J hdiag hJ i j k l m hm


-- created on 2026-10-23
