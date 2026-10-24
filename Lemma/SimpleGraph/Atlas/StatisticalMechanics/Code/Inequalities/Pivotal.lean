import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Inequalities.Pivotal
open StatMech


/--
[setOpen_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setOpen_self_eq
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  setOpen e ω e = true := by
-- proof
  apply StatMech.setOpen_self e ω

/--
[setClosed_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setClosed_self_eq
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  setClosed e ω e = false := by
-- proof
  apply StatMech.setClosed_self e ω

/--
[setOpen_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setOpen_of_ne_eq
  [DecidableEq E]
  {e e' : E}
  {ω : ConfigSpace E}
-- given
  (h : e' ≠ e) :
-- imply
  setOpen e ω e' = ω e' := by
-- proof
  apply StatMech.setOpen_of_ne h ω

/--
[setClosed_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setClosed_of_ne_eq
  [DecidableEq E]
  {e e' : E}
  {ω : ConfigSpace E}
-- given
  (h : e' ≠ e) :
-- imply
  setClosed e ω e' = ω e' := by
-- proof
  apply StatMech.setClosed_of_ne h ω

/--
[setClosed_le_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setClosed_le_setOpen_eq
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  setClosed e ω ≤ setOpen e ω := by
-- proof
  apply StatMech.setClosed_le_setOpen e ω

/--
[setOpen_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setOpen_congr_eq
  [DecidableEq E]
  {e : E}
  {ω ω' : ConfigSpace E}
-- given
  (h : ∀ e', e' ≠ e → ω e' = ω' e') :
-- imply
  setOpen e ω = setOpen e ω' := by
-- proof
  apply StatMech.setOpen_congr h

/--
[setClosed_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setClosed_congr_eq
  [DecidableEq E]
  {e : E}
  {ω ω' : ConfigSpace E}
-- given
  (h : ∀ e', e' ≠ e → ω e' = ω' e') :
-- imply
  setClosed e ω = setClosed e ω' := by
-- proof
  apply StatMech.setClosed_congr h

/--
[setOpen_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setOpen_setClosed_eq
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  setOpen e (setClosed e ω) = setOpen e ω := by
-- proof
  apply StatMech.setOpen_setClosed e ω

/--
[setClosed_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setClosed_setOpen_eq
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  setClosed e (setOpen e ω) = setClosed e ω := by
-- proof
  apply StatMech.setClosed_setOpen e ω

/--
[setOpen_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setOpen_setOpen_eq
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  setOpen e (setOpen e ω) = setOpen e ω := by
-- proof
  apply StatMech.setOpen_setOpen e ω

/--
[setClosed_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma setClosed_setClosed_eq
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  setClosed e (setClosed e ω) = setClosed e ω := by
-- proof
  apply StatMech.setClosed_setClosed e ω

/--
[isPivotal_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma isPivotal_comm_eq
  [DecidableEq E]
  {e : E}
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  IsPivotal e A ω ↔ (setClosed e ω ∈ A) ≠ (setOpen e ω ∈ A) := by
-- proof
  apply StatMech.isPivotal_comm e A ω

/--
[isPivotal_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma isPivotal_congr_eq
  [DecidableEq E]
  {e : E}
  {A : Set (ConfigSpace E)}
  {ω ω' : ConfigSpace E}
-- given
  (h : ∀ e', e' ≠ e → ω e' = ω' e') :
-- imply
  IsPivotal e A ω ↔ IsPivotal e A ω' := by
-- proof
  apply StatMech.isPivotal_congr h

/--
[isPivotal_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma isPivotal_setOpen_eq
  [DecidableEq E]
  {e : E}
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  IsPivotal e A (setOpen e ω) ↔ IsPivotal e A ω := by
-- proof
  apply StatMech.isPivotal_setOpen e A ω

/--
[isPivotal_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma isPivotal_setClosed_eq
  [DecidableEq E]
  {e : E}
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  IsPivotal e A (setClosed e ω) ↔ IsPivotal e A ω := by
-- proof
  apply StatMech.isPivotal_setClosed e A ω

/--
[isPivotal_iff_of_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Pivotal.lean)
-/
@[path]
private lemma isPivotal_iff_of_isIncreasing_eq
  [DecidableEq E]
  {e : E}
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsPivotal e A ω ↔ (setClosed e ω ∉ A ∧ setOpen e ω ∈ A) := by
-- proof
  apply StatMech.isPivotal_iff_of_isIncreasing hA ω


-- created on 2026-10-23
