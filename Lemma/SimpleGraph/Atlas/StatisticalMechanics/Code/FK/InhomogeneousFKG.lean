import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.InhomogeneousFKG
open StatMech StatMech.FK


/--
[edgeProductW_logModular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InhomogeneousFKG.lean)
-/
@[path]
private lemma edgeProductW_logModular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  edgeProductW G pf a * edgeProductW G pf b = edgeProductW G pf (a ⊔ b) * edgeProductW G pf (a ⊓ b) := by
-- proof
  apply StatMech.FK.edgeProductW_logModular G pf a b

/--
[fkWeightW_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InhomogeneousFKG.lean)
-/
@[path]
private lemma fkWeightW_logSupermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 1 ≤ q) :
-- imply
  fkWeightW G pf q a * fkWeightW G pf q b ≤ fkWeightW G pf q (a ⊔ b) * fkWeightW G pf q (a ⊓ b) := by
-- proof
  apply StatMech.FK.fkWeightW_logSupermodular G hpf hpf1 hq a b

/--
[fkProbW_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InhomogeneousFKG.lean)
-/
@[path]
private lemma fkProbW_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q) :
-- imply
  ∑ ω, fkProbW G pf q ω = 1 := by
-- proof
  apply StatMech.FK.fkProbW_sum_eq_one G hpf hpf1 hq

/--
[fkProbW_FKGLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InhomogeneousFKG.lean)
-/
@[path]
private lemma fkProbW_FKGLatticeCondition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 1 ≤ q) :
-- imply
  FKGLatticeCondition (fkProbW G pf q) := by
-- proof
  apply StatMech.FK.fkProbW_FKGLatticeCondition G hpf hpf1 hq

/--
[fkProbW_isMonotonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InhomogeneousFKG.lean)
-/
@[path]
private lemma fkProbW_isMonotonic_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 1 ≤ q) :
-- imply
  OSSS.Monotonic.IsMonotonicMeasure (fkProbW G pf q) := by
-- proof
  apply StatMech.FK.fkProbW_isMonotonic G hpf hpf1 hq

/--
[fkProbW_flipE_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InhomogeneousFKG.lean)
-/
@[path]
private lemma fkProbW_flipE_off_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ G.edgeFinset) :
-- imply
  fkProbW G pf q (OSSS.HBridgeClose.flipE e ω) = fkProbW G pf q ω := by
-- proof
  apply StatMech.FK.fkProbW_flipE_off G pf q he ω


-- created on 2026-10-23
