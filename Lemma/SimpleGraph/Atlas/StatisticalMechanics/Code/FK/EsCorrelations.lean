import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.EsCorrelations
open StatMech StatMech.FK


/--
[isingSpin_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma isingSpin_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : Fin 2} :
-- imply
  isingSpin a * isingSpin b = 2 * (if a = b then 1 else 0) - 1 := by
-- proof
  apply StatMech.FK.isingSpin_mul G a b

/--
[card_eqfun_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma card_eqfun_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype C]
  {q : ℕ}
  {a b : C}
-- given
  (hab : a ≠ b) :
-- imply
  Nat.card {f : C → Fin q // f a = f b} = q ^ (Fintype.card C - 1) := by
-- proof
  apply StatMech.FK.card_eqfun_ne G q hab

/--
[card_eqfun_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma card_eqfun_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype C]
  {q : ℕ}
  {a b : C}
-- given
  (hab : a = b) :
-- imply
  Nat.card {f : C → Fin q // f a = f b} = q ^ Fintype.card C := by
-- proof
  apply StatMech.FK.card_eqfun_eq G q hab

/--
[card_constEq_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma card_constEq_connected_eq
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
  Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ σ x = σ y} = q ^ numClusters G ω := by
-- proof
  apply StatMech.FK.card_constEq_connected G ω hxy

/--
[card_constEq_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma card_constEq_disconnected_eq
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
  Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ σ x = σ y} = q ^ (numClusters G ω - 1) := by
-- proof
  apply StatMech.FK.card_constEq_disconnected G ω hxy

/--
[one_le_numClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma one_le_numClusters_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)}
  {x : V} :
-- imply
  1 ≤ numClusters G ω := by
-- proof
  apply StatMech.FK.one_le_numClusters G ω x

/--
[card_const_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma card_const_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  ((Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ)).card : ℝ) = 2 ^ numClusters G ω := by
-- proof
  apply StatMech.FK.card_const_two G ω

/--
[esWeight_spinsum_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma esWeight_spinsum_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {g : (V → Fin 2) → ℝ} :
-- imply
  (∑ σ : V → Fin 2, esWeight G p σ ω * g σ) = edgeProduct G p ω * ∑ σ : V → Fin 2, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * g σ := by
-- proof
  apply StatMech.FK.esWeight_spinsum_factor G p ω g

/--
[inner_spin_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma inner_spin_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)}
  {x y : V} :
-- imply
  (∑ σ : V → Fin 2, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * (isingSpin (σ x) * isingSpin (σ y))) = 2 * (Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ ∧ σ x = σ y)).card - (Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ)).card := by
-- proof
  apply StatMech.FK.inner_spin_sum G ω x y

/--
[spinProd_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma spinProd_sum_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {x y : V} :
-- imply
  (∑ σ : V → Fin 2, esWeight G p σ ω * (isingSpin (σ x) * isingSpin (σ y))) = if Connected G ω x y then fkWeight G p (2 : ℝ) ω else 0 := by
-- proof
  apply StatMech.FK.spinProd_sum_eq G p ω x y

/--
[esTwoPoint_eq_connProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma esTwoPoint_eq_connProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {x y : V} :
-- imply
  esTwoPoint G p x y = connProb G p 2 x y := by
-- proof
  apply StatMech.FK.esTwoPoint_eq_connProb G p x y

/--
[connProb_eq_sum_fkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean)
-/
@[path]
private lemma connProb_eq_sum_fkProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x y : V} :
-- imply
  connProb G p q x y = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y), fkProb G p q ω := by
-- proof
  apply StatMech.FK.connProb_eq_sum_fkProb G p q x y


-- created on 2026-10-23
