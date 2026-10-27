import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.fc_doublingstep
open SimpleGraph Filter Topology Set StatMech StatMech.Walls


/--
[fc_doublingStep_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_doublingstep.lean)
-/
@[path]
private lemma fc_doublingStep_div_eq
  {a A c i e E K : ℝ}
-- given
  (he : 0 < e)
  (hE : 0 < E)
  (hdoub : A ≤ K * a + i * c)
  (hedge : |K * e - E| ≤ i) :
-- imply
  A / E - a / e ≤ (|a| / e + c) * (i / E) := by
-- proof
  apply StatMech.Walls.fc_doublingStep_div a A c i e E K he hE hdoub hedge

/--
[fc_doublingStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_doublingstep.lean)
-/
@[path]
private lemma fc_doublingStep_eq
  {a A c i e E K C : ℝ}
-- given
  (he : 0 < e)
  (hE : 0 < E)
  (hdoub : A ≤ K * a + i * c)
  (hedge : |K * e - E| ≤ i) :
-- imply
  (-a / e + C) - (|a| / e + c) * (i / E) ≤ (-A / E + C) := by
-- proof
  apply StatMech.Walls.fc_doublingStep a A c i e E K C he hE hdoub hedge

/--
[fc_doublingStep_freeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_doublingstep.lean)
-/
@[path]
private lemma fc_doublingStep_freeEnergy_eq
  {a A c i e E K C : ℝ}
-- given
  (he : 0 < e)
  (hE : 0 < E)
  (hdoub : A ≤ K * a + i * c)
  (hedge : |K * e - E| ≤ i) :
-- imply
  (fun (Ec u : ℝ) => -u / Ec + C) e a - (|a| / e + c) * (i / E) ≤ (fun (Ec u : ℝ) => -u / Ec + C) E A := by
-- proof
  apply StatMech.Walls.fc_doublingStep_freeEnergy a A c i e E K C he hE hdoub hedge

/--
[fc_deficit_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_doublingstep.lean)
-/
@[path]
private lemma fc_deficit_nonneg_eq
  {a c i e E : ℝ}
-- given
  (he : 0 < e)
  (hE : 0 < E)
  (hc : 0 ≤ c)
  (hi : 0 ≤ i) :
-- imply
  0 ≤ (|a| / e + c) * (i / E) := by
-- proof
  apply StatMech.Walls.fc_deficit_nonneg a c i e E he hE hc hi

/--
[fc_doublingStep_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_doublingstep.lean)
-/
@[path]
private lemma fc_doublingStep_satisfiable_eq
  {a e K C : ℝ}
-- given
  (he : 0 < e)
  (hK : 0 < K) :
-- imply
  let A := K * a; let E := K * e (A ≤ K * a + (0 : ℝ) * (0 : ℝ)) ∧ (|K * e - E| ≤ (0 : ℝ)) ∧ ((|a| / e + (0 : ℝ)) * ((0 : ℝ) / E) = 0) ∧ ((-a / e + C) - (|a| / e + (0 : ℝ)) * ((0 : ℝ) / E) ≤ (-A / E + C)) := by
-- proof
  apply StatMech.Walls.fc_doublingStep_satisfiable a e K C he hK


-- created on 2026-10-23
