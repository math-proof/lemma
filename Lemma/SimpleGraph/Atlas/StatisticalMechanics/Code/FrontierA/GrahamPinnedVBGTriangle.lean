import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGTriangle
open Finset Classical StatMech StatMech.FrontierA


/--
[vbg_coordUp_eq_half_one_add_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_coordUp_eq_half_one_add_spin_eq
  [Fintype V]
  [DecidableEq V]
  {m : V}
  {s : ConfigSpace V} :
-- imply
  vbg_coordUp m s = (1 + spin s m) / 2 := by
-- proof
  apply StatMech.FrontierA.vbg_coordUp_eq_half_one_add_spin m s

/--
[vbg_exp_grahamZeroProb_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_exp_grahamZeroProb_one_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_exp (grahamZeroProb E J) (fun _ => 1) = 1 := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamZeroProb_one E J

/--
[vbg_exp_grahamZeroProb_coordUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_exp_grahamZeroProb_coordUp_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_exp (grahamZeroProb E J) (vbg_coordUp m) = 1 / 2 := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamZeroProb_coordUp E J m

/--
[vbg_exp_grahamZeroProb_threeSpin_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_exp_grahamZeroProb_threeSpin_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {a b c : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_exp (grahamZeroProb E J) (fun s => spin s a * spin s b * spin s c) = 0 := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamZeroProb_threeSpin_eq_zero E J a b c

/--
[vbg_exp_grahamZeroProb_twoSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_exp_grahamZeroProb_twoSpin_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {a b : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_exp (grahamZeroProb E J) (fun s => spin s a * spin s b) = grahamTwoPoint E J a b := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamZeroProb_twoSpin E J a b

/--
[vbg_exp_grahamZeroProb_mul_coordUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_exp_grahamZeroProb_mul_coordUp_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (f : ConfigSpace V -> Real) :
-- imply
  (∑ s : ConfigSpace V, grahamZeroProb E J s * vbg_coordUp m s * f s) = (vbg_exp (grahamZeroProb E J) f + vbg_exp (grahamZeroProb E J) (fun s => f s * spin s m)) / 2 := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamZeroProb_mul_coordUp E J m f

/--
[vbg_exp_grahamPinnedProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_exp_grahamPinnedProb_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (f : ConfigSpace V -> Real) :
-- imply
  vbg_exp (grahamPinnedProb E J m) f = vbg_exp (grahamZeroProb E J) f + vbg_exp (grahamZeroProb E J) (fun s => f s * spin s m) := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamPinnedProb E J m f

/--
[vbg_exp_grahamPinnedProb_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_exp_grahamPinnedProb_spin_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m a : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_exp (grahamPinnedProb E J m) (fun s => spin s a) = grahamTwoPoint E J a m := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamPinnedProb_spin E J m a

/--
[vbg_exp_grahamPinnedProb_twoSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_exp_grahamPinnedProb_twoSpin_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m a b : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_exp (grahamPinnedProb E J m) (fun s => spin s a * spin s b) = grahamTwoPoint E J a b := by
-- proof
  apply StatMech.FrontierA.vbg_exp_grahamPinnedProb_twoSpin E J m a b

/--
[vbg_cov_grahamPinnedProb_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_cov_grahamPinnedProb_spin_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m a b : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_cov (grahamPinnedProb E J m) (fun s => spin s a) (fun s => spin s b) = grahamBridgeGap E J a b m := by
-- proof
  apply StatMech.FrontierA.vbg_cov_grahamPinnedProb_spin E J m a b

/--
[vbg_var_grahamPinnedProb_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_var_grahamPinnedProb_spin_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m k : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  vbg_var (grahamPinnedProb E J m) (fun s => spin s k) = 1 - grahamTwoPoint E J k m ^ 2 := by
-- proof
  apply StatMech.FrontierA.vbg_var_grahamPinnedProb_spin E J m k

/--
[grahamPinnedProb_FKG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma grahamPinnedProb_FKG_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e) :
-- imply
  StatMech.FKGLatticeCondition (grahamPinnedProb E J m) := by
-- proof
  apply StatMech.FrontierA.grahamPinnedProb_FKG E J hJ m

/--
[vbg_cov_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma vbg_cov_comm_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (mu : ConfigSpace V -> Real)
  (f g : ConfigSpace V -> Real) :
-- imply
  vbg_cov mu f g = vbg_cov mu g f := by
-- proof
  apply StatMech.FrontierA.vbg_cov_comm mu f g

/--
[grahamBridgeGap_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGTriangle.lean)
-/
@[path]
private lemma grahamBridgeGap_triangle_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i k j m : V}
-- given
  (J : Sym2 V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e) :
-- imply
  grahamBridgeGap E J i k m * grahamBridgeGap E J j k m <= (1 - grahamTwoPoint E J k m ^ 2) * grahamBridgeGap E J i j m := by
-- proof
  apply StatMech.FrontierA.grahamBridgeGap_triangle E J hJ i k j m


-- created on 2026-10-23
