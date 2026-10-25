import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedFieldAdapter.Part3
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamAnchorCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchorCoupling_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (hJ : forall e, 0 <= J e) :
-- imply
  forall e, 0 <= grahamAnchorCoupling J m e := by
-- proof
  apply StatMech.FrontierA.grahamAnchorCoupling_nonneg J m hJ

/--
[grahamAnchorField_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchorField_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (hJ : forall e, 0 <= J e) :
-- imply
  forall x, 0 <= grahamAnchorField E J m x := by
-- proof
  apply StatMech.FrontierA.grahamAnchorField_nonneg E J m hJ

/--
[grahamPinConfig_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamPinConfig_at_eq
  [Fintype V]
  [DecidableEq V]
  {m : V}
  {t : ConfigSpace V} :
-- imply
  grahamPinConfig m t m = true := by
-- proof
  apply StatMech.FrontierA.grahamPinConfig_at m t

/--
[grahamPinConfig_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamPinConfig_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {m : V}
  {t : ConfigSpace V}
  {x : V}
-- given
  (hxm : x ≠ m) :
-- imply
  grahamPinConfig m t x = t x := by
-- proof
  apply StatMech.FrontierA.grahamPinConfig_of_ne m t hxm

/--
[spin_grahamPinConfig_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma spin_grahamPinConfig_at_eq
  [Fintype V]
  [DecidableEq V]
  {m : V}
  {t : ConfigSpace V} :
-- imply
  spin (grahamPinConfig m t) m = 1 := by
-- proof
  apply StatMech.FrontierA.spin_grahamPinConfig_at m t

/--
[spin_grahamPinConfig_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma spin_grahamPinConfig_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {m : V}
  {t : ConfigSpace V}
  {x : V}
-- given
  (hxm : x ≠ m) :
-- imply
  spin (grahamPinConfig m t) x = spin t x := by
-- proof
  apply StatMech.FrontierA.spin_grahamPinConfig_of_ne m t hxm

/--
[grahamAnchor_incidentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchor_incidentSum_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
  {t : ConfigSpace V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag) :
-- imply
  (∑ e ∈ E.filter (fun e => m ∈ e), J e * bond (grahamPinConfig m t) e) = ∑ x, grahamAnchorField E J m x * spin t x := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_incidentSum E J hdiag m t

/--
[grahamAnchor_nonincidentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchor_nonincidentSum_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
  {t : ConfigSpace V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  (∑ e ∈ E, grahamAnchorCoupling J m e * bond t e) = ∑ e ∈ E.filter (fun e => m ∉ e), J e * bond t e := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_nonincidentSum E J m t

/--
[grahamAnchor_weight_eq_pin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchor_weight_eq_pin_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
  {t : ConfigSpace V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag) :
-- imply
  wJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) t = wJ E J (fun _ => 0) (grahamPinConfig m t) := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_weight_eq_pin E J hdiag m t

/--
[grahamAnchorSlice_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchorSlice_at_eq
  [Fintype V]
  [DecidableEq V]
  {m : V}
  {b : Bool}
-- given
  (eta : {x : V // x ≠ m} -> Bool) :
-- imply
  grahamAnchorSlice m b eta m = b := by
-- proof
  apply StatMech.FrontierA.grahamAnchorSlice_at m b eta

/--
[grahamAnchorSlice_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchorSlice_ne_eq
  [Fintype V]
  [DecidableEq V]
  {m : V}
  {b : Bool}
-- given
  (eta : {x : V // x ≠ m} -> Bool)
  (x : {x : V // x ≠ m}) :
-- imply
  grahamAnchorSlice m b eta x.1 = eta x := by
-- proof
  apply StatMech.FrontierA.grahamAnchorSlice_ne m b eta x

/--
[grahamPinConfig_anchorSlice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamPinConfig_anchorSlice_eq
  [Fintype V]
  [DecidableEq V]
  {m : V}
  {b : Bool}
-- given
  (eta : {x : V // x ≠ m} -> Bool) :
-- imply
  grahamPinConfig m (grahamAnchorSlice m b eta) = grahamAnchorSlice m true eta := by
-- proof
  apply StatMech.FrontierA.grahamPinConfig_anchorSlice m b eta

/--
[grahamAnchor_sum_eq_two_mul_trueSlice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchor_sum_eq_two_mul_trueSlice_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (F : ConfigSpace V -> Real)
  (hF : ∀ t, F (grahamPinConfig m t) = F t) :
-- imply
  (∑ t : ConfigSpace V, F t * wJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) t) = 2 * ∑ eta : {x : V // x ≠ m} -> Bool, F (grahamAnchorSlice m true eta) * wJ E J (fun _ => 0) (grahamAnchorSlice m true eta) := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_sum_eq_two_mul_trueSlice E J hdiag m F hF

/--
[graham_trueSlice_sum_eq_half_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma graham_trueSlice_sum_eq_half_Z_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  (∑ eta : {x : V // x ≠ m} -> Bool, wJ E J (fun _ => 0) (grahamAnchorSlice m true eta)) = ZJ E J (fun _ => 0) / 2 := by
-- proof
  apply StatMech.FrontierA.graham_trueSlice_sum_eq_half_Z E J m

/--
[grahamAnchor_ZJ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchor_ZJ_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag) :
-- imply
  ZJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) = ZJ E J (fun _ => 0) := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_ZJ_eq E J hdiag m

/--
[vbg_exp_grahamPinnedProb_eq_trueSlice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma vbg_exp_grahamPinnedProb_eq_trueSlice_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (F : ConfigSpace V -> Real) :
-- imply
  vbg_exp (grahamPinnedProb E J m) F = (2 * ∑ eta : {x : V // x ≠ m} -> Bool, F (grahamAnchorSlice m true eta) * wJ E J (fun _ => 0) (grahamAnchorSlice m true eta)) / ZJ E J (fun _ => 0) := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamPinnedProb_eq_trueSlice E J m F

/--
[grahamAnchor_expJ_eq_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchor_expJ_eq_pinned_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (F : ConfigSpace V -> Real)
  (hF : ∀ t, F (grahamPinConfig m t) = F t) :
-- imply
  expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) F = vbg_exp (grahamPinnedProb E J m) F := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_expJ_eq_pinned E J hdiag m F hF

/--
[grahamAnchor_onePoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchor_onePoint_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m x : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hxm : x ≠ m) :
-- imply
  expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) (fun t => spin t x) = grahamTwoPoint E J x m := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_onePoint_eq E J hdiag hxm

/--
[grahamAnchor_twoPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchor_twoPoint_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m x y : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hxm : x ≠ m)
  (hym : y ≠ m) :
-- imply
  expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) (fun t => spin t x * spin t y) = grahamTwoPoint E J x y := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_twoPoint_eq E J hdiag hxm hym

/--
[vbg_exp_grahamPinnedProb_threeSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma vbg_exp_grahamPinnedProb_threeSpin_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m i j k : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_exp (grahamPinnedProb E J m) (fun t => spin t i * (spin t j * spin t k)) = grahamFourPoint E J i j k m := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamPinnedProb_threeSpin E J m i j k

/--
[grahamAnchor_threePoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean)
-/
@[path]
private lemma grahamAnchor_threePoint_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m i j k : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (him : i ≠ m)
  (hjm : j ≠ m)
  (hkm : k ≠ m) :
-- imply
  expJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) (fun t => spin t i * (spin t j * spin t k)) = grahamFourPoint E J i j k m := by
-- proof
  apply StatMech.FrontierA.grahamAnchor_threePoint_eq E J hdiag him hjm hkm


-- created on 2026-10-23
