import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterZeroFieldSheet
open StatMech StatMech.Ising


/--
[replicaBridgeMoment_zeroField_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterZeroFieldSheet.lean)
-/
@[path]
private lemma replicaBridgeMoment_zeroField_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeMoment G J (fun _ => 0) sites (-r) = replicaBridgeMoment G J (fun _ => 0) sites r := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_zeroField_neg G J sites r

/--
[replicaBridgeFreeEnergy_zeroField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterZeroFieldSheet.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_zeroField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeFreeEnergy G J (fun _ => 0) sites r = 0 := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_zeroField G J sites r

/--
[replicaBridgeVariance_zeroField_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterZeroFieldSheet.lean)
-/
@[path]
private lemma replicaBridgeVariance_zeroField_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeVariance G J (fun _ => 0) sites (-r) = replicaBridgeVariance G J (fun _ => 0) sites r := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_zeroField_neg G J sites r

/--
[replicaBridgeFreeEnergy_zeroField_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterZeroFieldSheet.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_zeroField_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (sites : I -> V)
  (hr : 0 <= r) :
-- imply
  replicaBridgeFreeEnergy G J (fun _ => 0) sites r <= 2 * r * ∑ i : I, (expJ G.edgeFinset J (fun _ => 0) (fun s => spin s (sites i))) ^ 2 := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_zeroField_le G J sites r hr


-- created on 2026-10-23
