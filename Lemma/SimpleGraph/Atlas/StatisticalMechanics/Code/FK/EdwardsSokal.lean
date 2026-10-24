import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.EdwardsSokal
open StatMech StatMech.FK


/--
[esWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ esWeight G p σ ω := by
-- proof
  apply StatMech.FK.esWeight_nonneg G hp hp1 σ ω

/--
[constOnOpen_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma constOnOpen_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {ω : ConfigSpace (Sym2 V)}
  {σ : V → Fin q}
  {x y : V}
  {r : (openSub G ω).Reachable x y}
-- given
  (h : ConstOnOpen G ω σ) :
-- imply
  σ x = σ y := by
-- proof
  apply StatMech.FK.constOnOpen_reachable G ω σ h r

/--
[esEdgeFactor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esEdgeFactor_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)}
  {e : Sym2 V} :
-- imply
  esEdgeFactor p σ ω e = (if ω e then p else 1 - p) * (if ω e then Potts.monoIndicator σ e else 1) := by
-- proof
  apply StatMech.FK.esEdgeFactor_eq G p σ ω e

/--
[esWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esWeight_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  esWeight G p σ ω = edgeProduct G p ω * ∏ e ∈ G.edgeFinset, (if ω e then Potts.monoIndicator σ e else 1) := by
-- proof
  apply StatMech.FK.esWeight_factor G p σ ω

/--
[monoProd_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma monoProd_eq_indicator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  (∏ e ∈ G.edgeFinset, (if ω e then Potts.monoIndicator σ e else 1)) = if ConstOnOpen G ω σ then 1 else 0 := by
-- proof
  apply StatMech.FK.monoProd_eq_indicator G σ ω

/--
[card_constOnOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma card_constOnOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  Nat.card {σ : V → Fin q // ConstOnOpen G ω σ} = q ^ numClusters G ω := by
-- proof
  apply StatMech.FK.card_constOnOpen G ω

/--
[esWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esWeight_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  (∑ σ : V → Fin q, esWeight G p σ ω) = fkWeight G p (q : ℝ) ω := by
-- proof
  apply StatMech.FK.esWeight_sum G p ω

/--
[esWeight_eq_prod_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esWeight_eq_prod_univ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  esWeight G p σ ω = ∏ e : Sym2 V, esCoeff G p σ e (ω e) := by
-- proof
  apply StatMech.FK.esWeight_eq_prod_univ G p σ ω

/--
[esWeight_sum_omega](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esWeight_sum_omega_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {σ : V → Fin q} :
-- imply
  (∑ ω : ConfigSpace (Sym2 V), esWeight G p σ ω) = ∏ e : Sym2 V, ∑ b : Bool, esCoeff G p σ e b := by
-- proof
  apply StatMech.FK.esWeight_sum_omega G p σ

/--
[esCoeff_bool_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esCoeff_bool_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {σ : V → Fin q}
  {e : Sym2 V} :
-- imply
  (∑ b : Bool, esCoeff G p σ e b) = if e ∈ G.edgeFinset then (1 - p) + p * Potts.monoIndicator σ e else 2 := by
-- proof
  apply StatMech.FK.esCoeff_bool_sum G p σ e

/--
[edge_sum_eq_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma edge_sum_eq_exp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {β J : ℝ}
  {σ : V → Fin q}
  {e : Sym2 V} :
-- imply
  (1 - (1 - Real.exp (-(β * J)))) + (1 - Real.exp (-(β * J))) * Potts.monoIndicator σ e = Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) := by
-- proof
  apply StatMech.FK.edge_sum_eq_exp G β J σ e

/--
[esFirstConst_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esFirstConst_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β J : ℝ} :
-- imply
  0 < esFirstConst G β J := by
-- proof
  apply StatMech.FK.esFirstConst_pos G β J

/--
[esWeight_sum_eq_pottsWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esWeight_sum_eq_pottsWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {β J : ℝ}
  {σ : V → Fin q} :
-- imply
  (∑ ω : ConfigSpace (Sym2 V), esWeight G (1 - Real.exp (-(β * J))) σ ω) = esFirstConst G β J * Potts.pottsWeight G β J σ := by
-- proof
  apply StatMech.FK.esWeight_sum_eq_pottsWeight G β J σ

/--
[esZ_eq_fkZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esZ_eq_fkZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ} :
-- imply
  esZ G q p = fkZ G p (q : ℝ) := by
-- proof
  apply StatMech.FK.esZ_eq_fkZ G q p

/--
[esZ_eq_pottsZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esZ_eq_pottsZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ} :
-- imply
  esZ G q (1 - Real.exp (-(β * J))) = esFirstConst G β J * Potts.pottsZ G q β J := by
-- proof
  apply StatMech.FK.esZ_eq_pottsZ G q β J

/--
[esZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < (q : ℝ)) :
-- imply
  0 < esZ G q p := by
-- proof
  apply StatMech.FK.esZ_pos G hp hp1 hq

/--
[esSecondMarginal_eq_fkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esSecondMarginal_eq_fkProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  esSecondMarginal G q p ω = fkProb G p (q : ℝ) ω := by
-- proof
  apply StatMech.FK.esSecondMarginal_eq_fkProb G q p ω

/--
[esFirstMarginal_eq_pottsProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esFirstMarginal_eq_pottsProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {σ : V → Fin q} :
-- imply
  esFirstMarginal G q (1 - Real.exp (-(β * J))) σ = Potts.pottsProb G q β J σ := by
-- proof
  apply StatMech.FK.esFirstMarginal_eq_pottsProb G q β J σ

/--
[esSecondMarginal_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esSecondMarginal_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < (q : ℝ)) :
-- imply
  0 ≤ esSecondMarginal G q p ω := by
-- proof
  apply StatMech.FK.esSecondMarginal_nonneg G hp hp1 hq ω

/--
[esSecondMarginal_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esSecondMarginal_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < (q : ℝ)) :
-- imply
  (∑ ω : ConfigSpace (Sym2 V), esSecondMarginal G q p ω) = 1 := by
-- proof
  apply StatMech.FK.esSecondMarginal_sum_eq_one G hp hp1 hq

/--
[esFirstMarginal_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esFirstMarginal_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {σ : V → Fin q} :
-- imply
  0 ≤ esFirstMarginal G q (1 - Real.exp (-(β * J))) σ := by
-- proof
  apply StatMech.FK.esFirstMarginal_nonneg G β J σ

/--
[esFirstMarginal_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma esFirstMarginal_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ} :
-- imply
  (∑ σ : V → Fin q, esFirstMarginal G q (1 - Real.exp (-(β * J))) σ) = 1 := by
-- proof
  apply StatMech.FK.esFirstMarginal_sum_eq_one G β J

/--
[edwardsSokal_secondMarginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma edwardsSokal_secondMarginal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {β J : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  esSecondMarginal G q (1 - Real.exp (-(β * J))) ω = fkProb G (1 - Real.exp (-(β * J))) (q : ℝ) ω := by
-- proof
  apply StatMech.FK.edwardsSokal_secondMarginal G q β J ω

/--
[edwardsSokal_firstMarginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean)
-/
@[path]
private lemma edwardsSokal_firstMarginal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {σ : V → Fin q} :
-- imply
  esFirstMarginal G q (1 - Real.exp (-(β * J))) σ = Potts.pottsProb G q β J σ := by
-- proof
  apply StatMech.FK.edwardsSokal_firstMarginal G q β J σ


-- created on 2026-10-23
