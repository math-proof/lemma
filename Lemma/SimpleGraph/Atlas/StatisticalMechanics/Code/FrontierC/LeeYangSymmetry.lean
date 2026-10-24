import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry
open Finset Polynomial StatMech StatMech.FrontierC


/--
[leeYangFlip_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangFlip_apply_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {x : V} :
-- imply
  leeYangFlip s x = !(s x) := by
-- proof
  apply StatMech.FrontierC.leeYangFlip_apply s x

/--
[leeYangFlip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangFlip_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  leeYangFlip (leeYangFlip s) = s := by
-- proof
  apply StatMech.FrontierC.leeYangFlip_involutive s

/--
[leeYangFlipEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangFlipEquiv_apply_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  leeYangFlipEquiv s = leeYangFlip s := by
-- proof
  apply StatMech.FrontierC.leeYangFlipEquiv_apply s

/--
[minusSpinCount_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma minusSpinCount_flip_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  minusSpinCount (leeYangFlip s) = Fintype.card V - minusSpinCount s := by
-- proof
  apply StatMech.FrontierC.minusSpinCount_flip s

/--
[bond_leeYangFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma bond_leeYangFlip_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond (leeYangFlip s) e = bond s e := by
-- proof
  apply StatMech.FrontierC.bond_leeYangFlip s e

/--
[zeroFieldInteractionWeight_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma zeroFieldInteractionWeight_flip_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {s : ConfigSpace V} :
-- imply
  zeroFieldInteractionWeight G beta (leeYangFlip s) = zeroFieldInteractionWeight G beta s := by
-- proof
  apply StatMech.FrontierC.zeroFieldInteractionWeight_flip beta s

/--
[leeYangPolynomial_coeff_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangPolynomial_coeff_symm_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {k : ℕ}
-- given
  (hk : k ≤ Fintype.card V) :
-- imply
  (leeYangPolynomial G beta).coeff k = (leeYangPolynomial G beta).coeff (Fintype.card V - k) := by
-- proof
  apply StatMech.FrontierC.leeYangPolynomial_coeff_symm beta hk

/--
[leeYangPolynomial_natDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangPolynomial_natDegree_le_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  (leeYangPolynomial G beta).natDegree ≤ Fintype.card V := by
-- proof
  apply StatMech.FrontierC.leeYangPolynomial_natDegree_le beta

/--
[leeYangPolynomial_coeff_card_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangPolynomial_coeff_card_pos_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  0 < (leeYangPolynomial G beta).coeff (Fintype.card V) := by
-- proof
  apply StatMech.FrontierC.leeYangPolynomial_coeff_card_pos beta

/--
[leeYangPolynomial_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangPolynomial_natDegree_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  (leeYangPolynomial G beta).natDegree = Fintype.card V := by
-- proof
  apply StatMech.FrontierC.leeYangPolynomial_natDegree beta

/--
[leeYangPolynomial_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangPolynomial_reverse_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  (leeYangPolynomial G beta).reverse = leeYangPolynomial G beta := by
-- proof
  apply StatMech.FrontierC.leeYangPolynomial_reverse beta

/--
[leeYangComplexPolynomial_coeff_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_coeff_symm_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {k : ℕ}
-- given
  (hk : k ≤ Fintype.card V) :
-- imply
  (leeYangComplexPolynomial G beta).coeff k = (leeYangComplexPolynomial G beta).coeff (Fintype.card V - k) := by
-- proof
  apply StatMech.FrontierC.leeYangComplexPolynomial_coeff_symm beta hk

/--
[leeYangComplexPolynomial_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_natDegree_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  (leeYangComplexPolynomial G beta).natDegree = Fintype.card V := by
-- proof
  apply StatMech.FrontierC.leeYangComplexPolynomial_natDegree beta

/--
[leeYangComplexPolynomial_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_reverse_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  (leeYangComplexPolynomial G beta).reverse = leeYangComplexPolynomial G beta := by
-- proof
  apply StatMech.FrontierC.leeYangComplexPolynomial_reverse beta

/--
[leeYangPolynomial_coeff_zero_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangPolynomial_coeff_zero_pos_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  0 < (leeYangPolynomial G beta).coeff 0 := by
-- proof
  apply StatMech.FrontierC.leeYangPolynomial_coeff_zero_pos beta

/--
[leeYangComplexPolynomial_eval_zero_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_eval_zero_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  (leeYangComplexPolynomial G beta).eval 0 ≠ 0 := by
-- proof
  apply StatMech.FrontierC.leeYangComplexPolynomial_eval_zero_ne_zero beta

/--
[leeYangComplexPolynomial_eval_inv_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_eval_inv_eq_zero_iff_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ}
-- given
  (hz : z ≠ 0) :
-- imply
  (leeYangComplexPolynomial G beta).eval z⁻¹ = 0 ↔ (leeYangComplexPolynomial G beta).eval z = 0 := by
-- proof
  apply StatMech.FrontierC.leeYangComplexPolynomial_eval_inv_eq_zero_iff beta hz

/--
[leeYangComplexPolynomial_eval_inv_eq_zero_iff'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_eval_inv_eq_zero_iff'_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ} :
-- imply
  (leeYangComplexPolynomial G beta).eval z⁻¹ = 0 ↔ (leeYangComplexPolynomial G beta).eval z = 0 := by
-- proof
  apply StatMech.FrontierC.leeYangComplexPolynomial_eval_inv_eq_zero_iff' beta z

/--
[leeYangComplexPolynomial_root_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_root_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ}
-- given
  (hz : (leeYangComplexPolynomial G beta).eval z = 0) :
-- imply
  z ≠ 0 := by
-- proof
  apply StatMech.FrontierC.leeYangComplexPolynomial_root_ne_zero beta hz

/--
[leeYangComplexPolynomial_isRoot_inv_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_isRoot_inv_iff_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ} :
-- imply
  (leeYangComplexPolynomial G beta).IsRoot z⁻¹ ↔ (leeYangComplexPolynomial G beta).IsRoot z := by
-- proof
  apply StatMech.FrontierC.leeYangComplexPolynomial_isRoot_inv_iff beta z

/--
[leeYangComplexPolynomial_isRoot_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/LeeYangSymmetry.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_isRoot_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ}
-- given
  (hz : (leeYangComplexPolynomial G beta).IsRoot z) :
-- imply
  z ≠ 0 := by
-- proof
  apply StatMech.FrontierC.leeYangComplexPolynomial_isRoot_ne_zero beta hz


-- created on 2026-10-23
