import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.IsingFK.EsWired
open StatMech StatMech.IsingFK


/--
[esFree_spin_marginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma esFree_spin_marginal_eq
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
  apply StatMech.IsingFK.esFree_spin_marginal G q β J σ

/--
[esFree_edge_marginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma esFree_edge_marginal_eq
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
  apply StatMech.IsingFK.esFree_edge_marginal G q p ω

/--
[boundaryFixed_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma boundaryFixed_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {b : Fin q}
-- given
  (bdry : V → Prop) :
-- imply
  BoundaryFixed bdry b (fun _ => b) := by
-- proof
  apply StatMech.IsingFK.boundaryFixed_const G bdry b

/--
[pottsZWired_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma pottsZWired_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {β J : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  0 < pottsZWired G bdry q b β J := by
-- proof
  apply StatMech.IsingFK.pottsZWired_pos G bdry q b β J

/--
[pottsZWired_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma pottsZWired_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {β J : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  pottsZWired G bdry q b β J ≠ 0 := by
-- proof
  apply StatMech.IsingFK.pottsZWired_ne_zero G bdry q b β J

/--
[pottsProbWired_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma pottsProbWired_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {β J : ℝ}
  {σ : V → Fin q}
-- given
  (bdry : V → Prop) :
-- imply
  0 ≤ pottsProbWired G bdry q b β J σ := by
-- proof
  apply StatMech.IsingFK.pottsProbWired_nonneg G bdry q b β J σ

/--
[pottsProbWired_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma pottsProbWired_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {β J : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  (∑ σ : V → Fin q, pottsProbWired G bdry q b β J σ) = 1 := by
-- proof
  apply StatMech.IsingFK.pottsProbWired_sum_eq_one G bdry q b β J

/--
[pottsProbWired_eq_conditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma pottsProbWired_eq_conditional_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {β J : ℝ}
  {σ : V → Fin q}
-- given
  (bdry : V → Prop) :
-- imply
  pottsProbWired G bdry q b β J σ = if BoundaryFixed bdry b σ then Potts.pottsProb G q β J σ / (∑ τ : V → Fin q, if BoundaryFixed bdry b τ then Potts.pottsProb G q β J τ else 0) else 0 := by
-- proof
  apply StatMech.IsingFK.pottsProbWired_eq_conditional G bdry b β J σ

/--
[esWeightWired_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma esWeightWired_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {b : Fin q}
  {p : ℝ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hp : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ esWeightWired G bdry b p σ ω := by
-- proof
  apply StatMech.IsingFK.esWeightWired_nonneg G bdry hp hp1 σ ω

/--
[esWeightWired_sum_omega](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma esWeightWired_sum_omega_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {b : Fin q}
  {β J : ℝ}
  {σ : V → Fin q}
-- given
  (bdry : V → Prop) :
-- imply
  (∑ ω : ConfigSpace (Sym2 V), esWeightWired G bdry b (1 - Real.exp (-(β * J))) σ ω) = esFirstConst G β J * pottsWeightWired G bdry b β J σ := by
-- proof
  apply StatMech.IsingFK.esWeightWired_sum_omega G bdry b β J σ

/--
[esZWired_eq_pottsZWired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma esZWired_eq_pottsZWired_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {β J : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  esZWired G bdry q b (1 - Real.exp (-(β * J))) = esFirstConst G β J * pottsZWired G bdry q b β J := by
-- proof
  apply StatMech.IsingFK.esZWired_eq_pottsZWired G bdry b β J

/--
[esWiredFirstMarginal_eq_pottsProbWired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma esWiredFirstMarginal_eq_pottsProbWired_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {β J : ℝ}
  {σ : V → Fin q}
-- given
  (bdry : V → Prop) :
-- imply
  esWiredFirstMarginal G bdry q b (1 - Real.exp (-(β * J))) σ = pottsProbWired G bdry q b β J σ := by
-- proof
  apply StatMech.IsingFK.esWiredFirstMarginal_eq_pottsProbWired G bdry b β J σ

/--
[constOnWired_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma constOnWired_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {ω : ConfigSpace (Sym2 V)}
  {σ : V → Fin q}
  {x y : V}
  {r : (wiredSub G bdry ω).Reachable x y}
-- given
  (bdry : V → Prop)
  (h : ConstOnWired G bdry ω σ) :
-- imply
  σ x = σ y := by
-- proof
  apply StatMech.IsingFK.constOnWired_reachable G bdry ω σ h r

/--
[constOnOpen_boundaryFixed_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma constOnOpen_boundaryFixed_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {b : Fin q}
  {ω : ConfigSpace (Sym2 V)}
  {σ : V → Fin q}
-- given
  (bdry : V → Prop) :
-- imply
  (ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ) ↔ (ConstOnWired G bdry ω σ ∧ BoundaryFixed bdry b σ) := by
-- proof
  apply StatMech.IsingFK.constOnOpen_boundaryFixed_iff G bdry b ω σ

/--
[wiredSub_componentMk_eq_of_bdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma wiredSub_componentMk_eq_of_bdry_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {ω : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (bdry : V → Prop)
  (hx : bdry x)
  (hy : bdry y) :
-- imply
  (wiredSub G bdry ω).connectedComponentMk x = (wiredSub G bdry ω).connectedComponentMk y := by
-- proof
  apply StatMech.IsingFK.wiredSub_componentMk_eq_of_bdry G bdry hx hy

/--
[card_constOnOpen_boundaryFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma card_constOnOpen_boundaryFixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {b : Fin q}
  {ω : ConfigSpace (Sym2 V)}
  {v₀ : V}
-- given
  (bdry : V → Prop)
  (hv₀ : bdry v₀) :
-- imply
  Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ} = q ^ (numClustersBC G (boundaryCliqueGraph bdry) ω - 1) := by
-- proof
  apply StatMech.IsingFK.card_constOnOpen_boundaryFixed G bdry b ω v₀ hv₀

/--
[esWeightWired_sum_spins](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma esWeightWired_sum_spins_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {b : Fin q}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  (∑ σ : V → Fin q, esWeightWired G bdry b p σ ω) = edgeProduct G p ω * (Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ BoundaryFixed bdry b σ)).card := by
-- proof
  apply StatMech.IsingFK.esWeightWired_sum_spins G bdry b p ω

/--
[esWeightWired_sum_spins_eq_bcWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma esWeightWired_sum_spins_eq_bcWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {b : Fin q}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {v₀ : V}
-- given
  (bdry : V → Prop)
  (hv₀ : bdry v₀)
  (hq : 1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω) :
-- imply
  (q : ℝ) * (∑ σ : V → Fin q, esWeightWired G bdry b p σ ω) = bcWeight G (boundaryCliqueGraph bdry) p (q : ℝ) ω := by
-- proof
  apply StatMech.IsingFK.esWeightWired_sum_spins_eq_bcWeight G bdry b p ω v₀ hv₀ hq

/--
[esZWired_eq_bcZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma esZWired_eq_bcZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {b : Fin q}
  {p : ℝ}
  {v₀ : V}
-- given
  (bdry : V → Prop)
  (hv₀ : bdry v₀)
  (hq : ∀ ω : ConfigSpace (Sym2 V), 1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω) :
-- imply
  (q : ℝ) * esZWired G bdry q b p = bcZ G (boundaryCliqueGraph bdry) p (q : ℝ) := by
-- proof
  apply StatMech.IsingFK.esZWired_eq_bcZ G bdry b p v₀ hv₀ hq

/--
[esWiredSecondMarginal_eq_bcProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean)
-/
@[path]
private lemma esWiredSecondMarginal_eq_bcProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  {b : Fin q}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {v₀ : V}
-- given
  (bdry : V → Prop)
  (hv₀ : bdry v₀)
  (hqpos : 0 < q)
  (hq : ∀ ω : ConfigSpace (Sym2 V), 1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω) :
-- imply
  esWiredSecondMarginal G bdry q b p ω = bcProb G (boundaryCliqueGraph bdry) p (q : ℝ) ω := by
-- proof
  apply StatMech.IsingFK.esWiredSecondMarginal_eq_bcProb G bdry b p ω v₀ hv₀ hqpos hq


-- created on 2026-10-23
