import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kwd_hitempexpansion
open Finset StatMech StatMech.Walls


/--
[bond_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_hitempexpansion.lean)
-/
@[path]
private lemma bond_eq_one_or_neg_one_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond s e = 1 ∨ bond s e = -1 := by
-- proof
  apply StatMech.Walls.bond_eq_one_or_neg_one s e

/--
[exp_mul_eq_cosh_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_hitempexpansion.lean)
-/
@[path]
private lemma exp_mul_eq_cosh_mul_eq
  [Fintype V]
  [DecidableEq V]
  {β b : ℝ}
-- given
  (hb : b = 1 ∨ b = -1) :
-- imply
  Real.exp (β * b) = Real.cosh β * (1 + Real.tanh β * b) := by
-- proof
  apply StatMech.Walls.exp_mul_eq_cosh_mul β b hb

/--
[isingWeight_field_free_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_hitempexpansion.lean)
-/
@[path]
private lemma isingWeight_field_free_eq_prod_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ}
  {s : ConfigSpace V} :
-- imply
  isingWeight G β 0 s = ∏ e ∈ G.edgeFinset, Real.exp (β * bond s e) := by
-- proof
  apply StatMech.Walls.isingWeight_field_free_eq_prod β s

/--
[prod_exp_bond_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_hitempexpansion.lean)
-/
@[path]
private lemma prod_exp_bond_eq_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ}
  {s : ConfigSpace V} :
-- imply
  (∏ e ∈ G.edgeFinset, Real.exp (β * bond s e)) = (Real.cosh β) ^ G.edgeFinset.card * ∏ e ∈ G.edgeFinset, (1 + Real.tanh β * bond s e) := by
-- proof
  apply StatMech.Walls.prod_exp_bond_eq β s

/--
[prod_bond_eq_prod_pow_incCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_hitempexpansion.lean)
-/
@[path]
private lemma prod_bond_eq_prod_pow_incCount_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {F : Finset (Sym2 V)}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  (∏ e ∈ F, bond s e) = ∏ v : V, (spin s v) ^ (incCount F v) := by
-- proof
  apply StatMech.Walls.prod_bond_eq_prod_pow_incCount s F hF

/--
[spin_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_hitempexpansion.lean)
-/
@[path]
private lemma spin_pow_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {v : V}
  {n : ℕ} :
-- imply
  (spin s v) ^ n = if Even n then 1 else spin s v := by
-- proof
  apply StatMech.Walls.spin_pow s v n

/--
[sum_prod_spin_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_hitempexpansion.lean)
-/
@[path]
private lemma sum_prod_spin_set_eq
  [Fintype V]
  [DecidableEq V]
  {S : Finset V} :
-- imply
  (∑ s : ConfigSpace V, ∏ v ∈ S, spin s v) = if S = ∅ then (2 : ℝ) ^ Fintype.card V else 0 := by
-- proof
  apply StatMech.Walls.sum_prod_spin_set S

/--
[sum_prod_bond_subgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_hitempexpansion.lean)
-/
@[path]
private lemma sum_prod_bond_subgraph_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  (∑ s : ConfigSpace V, ∏ e ∈ F, bond s e) = if IsEvenSubgraph F then (2 : ℝ) ^ Fintype.card V else 0 := by
-- proof
  apply StatMech.Walls.sum_prod_bond_subgraph F hF

/--
[isingZ_high_temp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_hitempexpansion.lean)
-/
@[path]
private lemma isingZ_high_temp_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ} :
-- imply
  isingZ G β 0 = (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ G.edgeFinset.card * ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, (Real.tanh β) ^ F.card := by
-- proof
  apply StatMech.Walls.isingZ_high_temp β


-- created on 2026-10-23
