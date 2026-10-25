import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
open MeasureTheory StatMech StatMech.IsingFK


/--
[isingBond_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma isingBond_mk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {σ : V → Fin 2}
  {x y : V}
-- given
  (bdry : V → Prop) :
-- imply
  isingBond σ s(x, y) = isingSpin (σ x) * isingSpin (σ y) := by
-- proof
  apply StatMech.IsingFK.isingBond_mk G bdry σ x y

/--
[monoIndicator_eq_isingBond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma monoIndicator_eq_isingBond_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {σ : V → Fin 2}
  {e : Sym2 V}
-- given
  (bdry : V → Prop) :
-- imply
  monoIndicator σ e = isingBond σ e / 2 + 1 / 2 := by
-- proof
  apply StatMech.IsingFK.monoIndicator_eq_isingBond G bdry σ e

/--
[agreement_eq_isingBondSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma agreement_eq_isingBondSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {σ : V → Fin 2}
-- given
  (bdry : V → Prop) :
-- imply
  agreement G σ = (∑ e ∈ G.edgeFinset, isingBond σ e) / 2 + (G.edgeFinset.card : ℝ) / 2 := by
-- proof
  apply StatMech.IsingFK.agreement_eq_isingBondSum G bdry σ

/--
[pottsWeightWired_eq_isingWiredWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma pottsWeightWired_eq_isingWiredWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {β : ℝ}
  {σ : V → Fin 2}
-- given
  (bdry : V → Prop) :
-- imply
  pottsWeightWired G bdry (0 : Fin 2) (2 * β) 1 σ = Real.exp (β * G.edgeFinset.card) * isingWiredWeight G bdry β σ := by
-- proof
  apply StatMech.IsingFK.pottsWeightWired_eq_isingWiredWeight G bdry β σ

/--
[esWiredOnePoint_eq_pottsWiredOnePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma esWiredOnePoint_eq_pottsWiredOnePoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {β J : ℝ}
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  esWiredOnePoint G bdry (0 : Fin 2) (1 - Real.exp (-(β * J))) x = (∑ σ : V → Fin 2, pottsWeightWired G bdry (0 : Fin 2) β J σ * isingSpin (σ x)) / pottsZWired G bdry 2 (0 : Fin 2) β J := by
-- proof
  apply StatMech.IsingFK.esWiredOnePoint_eq_pottsWiredOnePoint G bdry β J x

/--
[esWiredOnePoint_eq_isingWiredOnePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma esWiredOnePoint_eq_isingWiredOnePoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {β : ℝ}
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  esWiredOnePoint G bdry (0 : Fin 2) (1 - Real.exp (-2 * β)) x = isingWiredOnePoint G bdry β x := by
-- proof
  apply StatMech.IsingFK.esWiredOnePoint_eq_isingWiredOnePoint G bdry β x

/--
[esWiredOnePoint_pOfBeta_eq_isingWiredOnePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma esWiredOnePoint_pOfBeta_eq_isingWiredOnePoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {β : ℝ}
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  esWiredOnePoint G bdry (0 : Fin 2) (pOfBeta β) x = isingWiredOnePoint G bdry β x := by
-- proof
  apply StatMech.IsingFK.esWiredOnePoint_pOfBeta_eq_isingWiredOnePoint G bdry β x

/--
[fvMagnetization_eq_fvProb_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma fvMagnetization_eq_fvProb_sum_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {n : ℕ} :
-- imply
  fvMagnetization d β n = ∑ τ : {x // x ∈ box d n} → Bool, fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ * spin (glue (plusField d) τ) (origin d) := by
-- proof
  apply StatMech.IsingFK.fvMagnetization_eq_fvProb_sum d β n

/--
[isingSpin_bToF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma isingSpin_bToF_eq
  {d : ℕ}
  {b : Bool} :
-- imply
  isingSpin (bToF b) = (if b then (1 : ℝ) else -1) := by
-- proof
  apply StatMech.IsingFK.isingSpin_bToF b

/--
[isingSpin_latToBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma isingSpin_latToBox_eq
  {d : ℕ}
  {d n : ℕ}
  {v : boxVerts d (n + 1)}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  isingSpin (latToBox d n τ v) = spin (glue (plusField d) τ) (v : Site d) := by
-- proof
  apply StatMech.IsingFK.isingSpin_latToBox d n τ v

/--
[boundaryFixed_latToBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean)
-/
@[path]
private lemma boundaryFixed_latToBox_eq
  {d : ℕ}
  {d n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) (latToBox d n τ) := by
-- proof
  apply StatMech.IsingFK.boundaryFixed_latToBox d n τ


-- created on 2026-10-23
