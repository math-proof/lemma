import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.RSW.SelfDualityNode.Part5
open MeasureTheory StatMech StatMech.RSW


/--
[rsd_dualParam_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_dualParam_coupling_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  rsd_dualCoupling p (BeffaraDC.dualParam p q) q := by
-- proof
  apply StatMech.RSW.rsd_dualParam_coupling hp hp1 hq

/--
[rsd_selfDualPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_selfDualPoint_eq_eq
  {q : ℝ} :
-- imply
  rsd_selfDualPoint q = BeffaraDC.selfDualPoint q := by
-- proof
  apply StatMech.RSW.rsd_selfDualPoint_eq q

/--
[rsd_selfDualPoint_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_selfDualPoint_mem_Ioo_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  rsd_selfDualPoint q ∈ Set.Ioo (0 : ℝ) 1 := by
-- proof
  apply StatMech.RSW.rsd_selfDualPoint_mem_Ioo hq

/--
[rsd_selfDual_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_selfDual_coupling_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  rsd_dualCoupling (rsd_selfDualPoint q) (rsd_selfDualPoint q) q := by
-- proof
  apply StatMech.RSW.rsd_selfDual_coupling hq

/--
[rsd_selfDual_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_selfDual_iff_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  BeffaraDC.dualParam p q = p ↔ p = rsd_selfDualPoint q := by
-- proof
  apply StatMech.RSW.rsd_selfDual_iff hp hp1 hq

/--
[rsd_dualBC_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_dualBC_wired_eq :
-- imply
  rsd_dualBC .wired = .free := by
-- proof
  apply StatMech.RSW.rsd_dualBC_wired

/--
[rsd_dualBC_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_dualBC_free_eq :
-- imply
  rsd_dualBC .free = .wired := by
-- proof
  apply StatMech.RSW.rsd_dualBC_free

/--
[rsd_dualBC_dualBC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_dualBC_dualBC_eq
  {bc : rsd_BC} :
-- imply
  rsd_dualBC (rsd_dualBC bc) = bc := by
-- proof
  apply StatMech.RSW.rsd_dualBC_dualBC bc

/--
[rsd_edgeCompl_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_edgeCompl_invol_eq
  [Fintype V]
  [DecidableEq V]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  rsd_edgeCompl (rsd_edgeCompl ω) = ω := by
-- proof
  apply StatMech.RSW.rsd_edgeCompl_invol ω

/--
[rsd_edgeProduct_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_edgeProduct_compl_eq
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  FK.edgeProduct G p (rsd_edgeCompl ω) = FK.edgeProduct G (1 - p) ω := by
-- proof
  apply StatMech.RSW.rsd_edgeProduct_compl p ω

/--
[rsd_fkZ_q1_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_fkZ_q1_dual_eq
  [Fintype V]
  [DecidableEq V]
  {p : ℝ} :
-- imply
  FK.fkZ G p 1 = FK.fkZ G (1 - p) 1 := by
-- proof
  apply StatMech.RSW.rsd_fkZ_q1_dual p

/--
[rsd_fkProb_q1_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_fkProb_q1_dual_eq
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  FK.fkProb G p 1 (rsd_edgeCompl ω) = FK.fkProb G (1 - p) 1 ω := by
-- proof
  apply StatMech.RSW.rsd_fkProb_q1_dual p ω

/--
[rsd_fkLaw_q1_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_fkLaw_q1_dual_eq
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
  {A : Finset (ConfigSpace (Sym2 V))} :
-- imply
  ∑ ω ∈ A.map (rsd_edgeComplEquiv (V := V)).toEmbedding, FK.fkProb G p 1 ω = ∑ ω ∈ A, FK.fkProb G (1 - p) 1 ω := by
-- proof
  apply StatMech.RSW.rsd_fkLaw_q1_dual p A

/--
[rsd_fkSelfDual_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_fkSelfDual_half_eq
  [Fintype V]
  [DecidableEq V]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  FK.fkProb G (1 / 2) 1 (rsd_edgeCompl ω) = FK.fkProb G (1 / 2) 1 ω := by
-- proof
  apply StatMech.RSW.rsd_fkSelfDual_half ω

/--
[rsd_fkLaw_selfDual_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_fkLaw_selfDual_half_eq
  [Fintype V]
  [DecidableEq V]
  {A : Finset (ConfigSpace (Sym2 V))} :
-- imply
  ∑ ω ∈ A.map (rsd_edgeComplEquiv (V := V)).toEmbedding, FK.fkProb G (1 / 2) 1 ω = ∑ ω ∈ A, FK.fkProb G (1 / 2) 1 ω := by
-- proof
  apply StatMech.RSW.rsd_fkLaw_selfDual_half A

/--
[rsd_selfDualPoint_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_selfDualPoint_one_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  rsd_selfDualPoint 1 = 1 / 2 := by
-- proof
  apply StatMech.RSW.rsd_selfDualPoint_one

/--
[rsd_planarDual_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_planarDual_law_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Measure.map Lattice.dualConfig (bernoulliProductMeasure p hp) = bernoulliProductMeasure (1 - p) tsub_le_self := by
-- proof
  apply StatMech.RSW.rsd_planarDual_law p hp

/--
[rsd_planarDual_selfDual_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_planarDual_selfDual_half_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  Measure.map Lattice.dualConfig (bernoulliProductMeasure (2⁻¹ : ℝ≥0) Universality.half_le_one) = bernoulliProductMeasure (2⁻¹ : ℝ≥0) Universality.half_le_one := by
-- proof
  apply StatMech.RSW.rsd_planarDual_selfDual_half

/--
[rsd_planarDual_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean)
-/
@[path]
private lemma rsd_planarDual_invol_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Measure.map Lattice.dualConfig (Measure.map Lattice.dualConfig (bernoulliProductMeasure p hp)) = bernoulliProductMeasure p hp := by
-- proof
  apply StatMech.RSW.rsd_planarDual_invol p hp


-- created on 2026-10-23
