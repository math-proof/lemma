import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGMoments
open Finset Classical StatMech StatMech.FrontierA


/--
[vbg_exp_grahamPinnedProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGMoments.lean)
-/
@[path]
private lemma vbg_exp_grahamPinnedProb_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (f : ConfigSpace V -> Real) :
-- imply
  vbg_exp (grahamPinnedProb E J m) f = vbg_exp (grahamZeroProb E J) (fun s => vbg_coordUp m s * f s) / vbg_exp (grahamZeroProb E J) (vbg_coordUp m) := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamPinnedProb_eq E J m f

/--
[grahamZeroProb_coordUp_eq_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGMoments.lean)
-/
@[path]
private lemma grahamZeroProb_coordUp_eq_half_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_exp (grahamZeroProb E J) (vbg_coordUp m) = (1 : Real) / 2 := by
-- proof
  apply StatMech.FrontierA.grahamZeroProb_coordUp_eq_half E J m

/--
[grahamPinnedProb_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGMoments.lean)
-/
@[path]
private lemma grahamPinnedProb_spin_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m x : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_exp (grahamPinnedProb E J m) (fun s => spin s x) = expJ E J (fun _ => 0) (fun s => spin s x * spin s m) := by
-- proof
  apply StatMech.FrontierA.grahamPinnedProb_spin E J m x

/--
[grahamPinnedProb_twoSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGMoments.lean)
-/
@[path]
private lemma grahamPinnedProb_twoSpin_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m x y : V}
-- given
  (J : Sym2 V -> Real)
  (hxy : x ≠ y)
  (hxm : x ≠ m)
  (hym : y ≠ m) :
-- imply
  vbg_exp (grahamPinnedProb E J m) (fun s => spin s x * spin s y) = expJ E J (fun _ => 0) (fun s => spin s x * spin s y) := by
-- proof
  apply StatMech.FrontierA.grahamPinnedProb_twoSpin E J hxy hxm hym


-- created on 2026-10-23
