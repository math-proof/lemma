import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeGraham
open Finset SimpleGraph StatMech StatMech.Ising


/--
[grahamInhomThreePoint_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeGraham.lean)
-/
@[path]
private lemma grahamInhomThreePoint_le_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  expJ G.edgeFinset K hf (fun s => spin s i * (spin s j * spin s k)) <= grahamInhomOne G K hf i * expJ G.edgeFinset K hf (fun s => spin s j * spin s k) + expJ G.edgeFinset K hf (fun s => spin s i * spin s j) * grahamInhomOne G K hf k + expJ G.edgeFinset K hf (fun s => spin s i * spin s k) * grahamInhomOne G K hf j - 2 * grahamInhomOne G K hf i * grahamInhomOne G K hf j * grahamInhomOne G K hf k - 2 * ghsiCovariance G K hf i k * ghsiCovariance G K hf j k * grahamInhomOne G K hf k := by
-- proof
  apply StatMech.Ising.grahamInhomThreePoint_le K hf hK hhf i j k

/--
[grahamInhomThreePoint_strong_cleared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeGraham.lean)
-/
@[path]
private lemma grahamInhomThreePoint_strong_cleared_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  2 * expJ G.edgeFinset K hf (fun s => spin s k) * (expJ G.edgeFinset K hf (fun s => spin s i * spin s k) - expJ G.edgeFinset K hf (fun s => spin s i) * expJ G.edgeFinset K hf (fun s => spin s k)) * (expJ G.edgeFinset K hf (fun s => spin s j * spin s k) - expJ G.edgeFinset K hf (fun s => spin s j) * expJ G.edgeFinset K hf (fun s => spin s k)) <= (1 - expJ G.edgeFinset K hf (fun s => spin s k) ^ 2) * (expJ G.edgeFinset K hf (fun s => spin s i) * expJ G.edgeFinset K hf (fun s => spin s j * spin s k) + expJ G.edgeFinset K hf (fun s => spin s i * spin s j) * expJ G.edgeFinset K hf (fun s => spin s k) + expJ G.edgeFinset K hf (fun s => spin s i * spin s k) * expJ G.edgeFinset K hf (fun s => spin s j) - 2 * expJ G.edgeFinset K hf (fun s => spin s i) * expJ G.edgeFinset K hf (fun s => spin s j) * expJ G.edgeFinset K hf (fun s => spin s k) - expJ G.edgeFinset K hf (fun s => spin s i * (spin s j * spin s k))) := by
-- proof
  apply StatMech.Ising.grahamInhomThreePoint_strong_cleared K hf hK hhf i j k

/--
[grahamInhomThreePoint_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeGraham.lean)
-/
@[path]
private lemma grahamInhomThreePoint_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  0 <= expJ G.edgeFinset K hf (fun s => spin s i * (spin s j * spin s k)) := by
-- proof
  apply StatMech.Ising.grahamInhomThreePoint_nonneg K hf hK hhf hij hik hjk

/--
[sq_grahamInhomThreePoint_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeGraham.lean)
-/
@[path]
private lemma sq_grahamInhomThreePoint_le_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  (expJ G.edgeFinset K hf (fun s => spin s i * (spin s j * spin s k))) ^ 2 <= (grahamInhomOne G K hf i * expJ G.edgeFinset K hf (fun s => spin s j * spin s k) + expJ G.edgeFinset K hf (fun s => spin s i * spin s j) * grahamInhomOne G K hf k + expJ G.edgeFinset K hf (fun s => spin s i * spin s k) * grahamInhomOne G K hf j - 2 * grahamInhomOne G K hf i * grahamInhomOne G K hf j * grahamInhomOne G K hf k - 2 * ghsiCovariance G K hf i k * ghsiCovariance G K hf j k * grahamInhomOne G K hf k) ^ 2 := by
-- proof
  apply StatMech.Ising.sq_grahamInhomThreePoint_le K hf hK hhf hij hik hjk


-- created on 2026-10-23
