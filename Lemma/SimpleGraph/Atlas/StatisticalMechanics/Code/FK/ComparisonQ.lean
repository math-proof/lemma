import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.ComparisonQ
open MeasureTheory SimpleGraph StatMech StatMech.FK


/--
[qFactor_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonQ.lean)
-/
@[path]
private lemma qFactor_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q₁ q₂ : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hq₁ : 1 ≤ q₁)
  (hq₁₂ : q₁ ≤ q₂) :
-- imply
  q₂ ^ numClusters G a * q₁ ^ numClusters G b ≤ q₂ ^ numClusters G (a ⊓ b) * q₁ ^ numClusters G (a ⊔ b) := by
-- proof
  apply StatMech.FK.qFactor_cross G hq₁ hq₁₂ a b

/--
[fkWeight_cross_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonQ.lean)
-/
@[path]
private lemma fkWeight_cross_q_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q₁ q₂ : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq₁ : 1 ≤ q₁)
  (hq₁₂ : q₁ ≤ q₂) :
-- imply
  fkWeight G p q₂ a * fkWeight G p q₁ b ≤ fkWeight G p q₂ (a ⊓ b) * fkWeight G p q₁ (a ⊔ b) := by
-- proof
  apply StatMech.FK.fkWeight_cross_q G hp hp1 hq₁ hq₁₂ a b

/--
[fkProb_cross_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonQ.lean)
-/
@[path]
private lemma fkProb_cross_q_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q₁ q₂ : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq₁ : 1 ≤ q₁)
  (hq₁₂ : q₁ ≤ q₂) :
-- imply
  fkProb G p q₂ a * fkProb G p q₁ b ≤ fkProb G p q₂ (a ⊓ b) * fkProb G p q₁ (a ⊔ b) := by
-- proof
  apply StatMech.FK.fkProb_cross_q G hp hp1 hq₁ hq₁₂ a b

/--
[fk_antitone_in_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonQ.lean)
-/
@[path]
private lemma fk_antitone_in_q_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q₁ q₂ : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq₁ : 1 ≤ q₁)
  (hq₁₂ : q₁ ≤ q₂) :
-- imply
  measOfMass (fkProb G p q₂) ≼ measOfMass (fkProb G p q₁) := by
-- proof
  apply StatMech.FK.fk_antitone_in_q G hp hp1 hq₁ hq₁₂


-- created on 2026-10-23
