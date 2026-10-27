import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokalFull.Part2
open StatMech StatMech.FK


/--
[esWeight_spinsum_factor_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean)
-/
@[path]
private lemma esWeight_spinsum_factor_q_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {g : (V → Fin q) → ℝ} :
-- imply
  (∑ σ : V → Fin q, esWeight G p σ ω * g σ) = edgeProduct G p ω * ∑ σ : V → Fin q, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * g σ := by
-- proof
  apply StatMech.FK.esWeight_spinsum_factor_q G p ω g

/--
[card_constEq_real_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean)
-/
@[path]
private lemma card_constEq_real_conn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {ω : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (hxy : Connected G ω x y) :
-- imply
  ((Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ) = (q : ℝ) ^ numClusters G ω := by
-- proof
  apply StatMech.FK.card_constEq_real_conn G ω hxy

/--
[card_constEq_real_disc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean)
-/
@[path]
private lemma card_constEq_real_disc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {ω : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (hxy : ¬ Connected G ω x y) :
-- imply
  ((Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ) = (q : ℝ) ^ (numClusters G ω - 1) := by
-- proof
  apply StatMech.FK.card_constEq_real_disc G ω hxy

/--
[spinAgree_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean)
-/
@[path]
private lemma spinAgree_sum_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {x y : V} :
-- imply
  (∑ σ : V → Fin q, esWeight G p σ ω * (if σ x = σ y then (1 : ℝ) else 0)) = if Connected G ω x y then fkWeight G p (q : ℝ) ω else fkWeight G p (q : ℝ) ω / q := by
-- proof
  apply StatMech.FK.spinAgree_sum_eq G p ω x y

/--
[pottsAgreeProb_eq_joint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean)
-/
@[path]
private lemma pottsAgreeProb_eq_joint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {x y : V} :
-- imply
  pottsAgreeProb G q β J x y = (∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin q, esWeight G (1 - Real.exp (-(β * J))) σ ω * (if σ x = σ y then (1 : ℝ) else 0)) / esZ G q (1 - Real.exp (-(β * J))) := by
-- proof
  apply StatMech.FK.pottsAgreeProb_eq_joint G q β J x y

/--
[edwards_sokal_correlation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean)
-/
@[path]
private lemma edwards_sokal_correlation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {x y : V}
-- given
  (hp : 0 < 1 - Real.exp (-(β * J)))
  (hp1 : 1 - Real.exp (-(β * J)) < 1)
  (hq : 0 < (q : ℝ)) :
-- imply
  pottsAgreeProb G q β J x y - 1 / q = (1 - 1 / q) * connProb G (1 - Real.exp (-(β * J))) q x y := by
-- proof
  apply StatMech.FK.edwards_sokal_correlation G q β J x y hp hp1 hq

/--
[edwards_sokal_correlation'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean)
-/
@[path]
private lemma edwards_sokal_correlation'_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {x y : V}
-- given
  (hp : 0 < 1 - Real.exp (-(β * J)))
  (hp1 : 1 - Real.exp (-(β * J)) < 1)
  (hq : 0 < (q : ℝ)) :
-- imply
  pottsAgreeProb G q β J x y - 1 / q = ((q : ℝ) - 1) / q * connProb G (1 - Real.exp (-(β * J))) q x y := by
-- proof
  apply StatMech.FK.edwards_sokal_correlation' G q β J x y hp hp1 hq

/--
[pottsAgreeProb_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean)
-/
@[path]
private lemma pottsAgreeProb_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {x y : V}
-- given
  (hp : 0 < 1 - Real.exp (-(β * J)))
  (hp1 : 1 - Real.exp (-(β * J)) < 1)
  (hq : 2 ≤ q) :
-- imply
  1 / q ≤ pottsAgreeProb G q β J x y := by
-- proof
  apply StatMech.FK.pottsAgreeProb_ge G q β J x y hp hp1 hq


-- created on 2026-10-23
