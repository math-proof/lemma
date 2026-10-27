import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.SigmaOrder
open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

/--
[bilinForm_sigma_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SigmaOrder.lean)
-/
@[path]
private lemma bilinForm_sigma_e
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v : B → ℝ} :
-- imply
  bilinForm M (sigma M s v) (e s) = -bilinForm M v (e s) := by
-- proof
  rw [bilinForm_sigma_general, formVal_diag]
  ring

end CoxeterGroup

namespace CoxeterGroup

/--
[sigma_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SigmaOrder.lean)
-/
@[path]
private lemma sigma_sq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B} :
-- imply
  sigmaLin M s * sigmaLin M s = 1 := by
-- proof
  apply LinearMap.ext; intro v
  change sigma M s (sigma M s v) = v
  ext t
  simp only [sigma, bilinForm_sigma_e]
  ring

end CoxeterGroup

namespace CoxeterGroup

/--
[sigmaLin_e_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SigmaOrder.lean)
-/
@[path]
private lemma sigmaLin_e_self
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B} :
-- imply
  sigmaLin M s (e s) = -e s := by
-- proof
  ext t
  show sigma M s (e s) t = (-e s) t
  simp only [sigma, bilinForm_e_e, formVal_diag, Pi.neg_apply]
  ring

end CoxeterGroup

/--
[bilinForm_sigma_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SigmaOrder.lean)
-/
@[path]
private lemma bilinForm_sigma_general_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ} :
-- imply
  bilinForm M (sigma M t v) (e s) = bilinForm M v (e s) - 2 * bilinForm M v (e t) * formVal M t s := by
-- proof
  apply CoxeterGroup.bilinForm_sigma_general M s t v

/--
[sigmaLin_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SigmaOrder.lean)
-/
@[path]
private lemma sigmaLin_e_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t) :
-- imply
  sigmaLin M s (e t) = fun u => e t u - 2 * formVal M s t * e s u := by
-- proof
  apply CoxeterGroup.sigmaLin_e M s t hst


-- created on 2026-10-23
-- updated on 2026-10-26
