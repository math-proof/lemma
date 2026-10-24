import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.Comparison
open Matrix Module StatMech StatMech.FK


/--
[mem_kerLap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma mem_kerLap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)}
  {x : V → ℝ} :
-- imply
  x ∈ kerLap G ω ↔ ∀ i j, (openSub G ω).Adj i j → x i = x j := by
-- proof
  apply StatMech.FK.mem_kerLap G ω x

/--
[numClusters_eq_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma numClusters_eq_finrank_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  numClusters G ω = Module.finrank ℝ (kerLap G ω) := by
-- proof
  apply StatMech.FK.numClusters_eq_finrank G ω

/--
[openSub_sup_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma openSub_sup_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)}
  {i j : V} :
-- imply
  (openSub G (a ⊔ b)).Adj i j ↔ (openSub G a).Adj i j ∨ (openSub G b).Adj i j := by
-- proof
  apply StatMech.FK.openSub_sup_adj G a b i j

/--
[openSub_inf_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma openSub_inf_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)}
  {i j : V} :
-- imply
  (openSub G (a ⊓ b)).Adj i j ↔ (openSub G a).Adj i j ∧ (openSub G b).Adj i j := by
-- proof
  apply StatMech.FK.openSub_inf_adj G a b i j

/--
[kerLap_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma kerLap_sup_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  kerLap G (a ⊔ b) = kerLap G a ⊓ kerLap G b := by
-- proof
  apply StatMech.FK.kerLap_sup G a b

/--
[kerLap_inf_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma kerLap_inf_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  kerLap G a ⊔ kerLap G b ≤ kerLap G (a ⊓ b) := by
-- proof
  apply StatMech.FK.kerLap_inf_ge G a b

/--
[numClusters_supermodular_lap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma numClusters_supermodular_lap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  numClusters G a + numClusters G b ≤ numClusters G (a ⊔ b) + numClusters G (a ⊓ b) := by
-- proof
  apply StatMech.FK.numClusters_supermodular_lap G a b

/--
[edgeFactor_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma edgeFactor_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 : ℝ}
  {α β : Bool}
-- given
  (hle : p1 ≤ p2) :
-- imply
  (if α then p1 else 1 - p1) * (if β then p2 else 1 - p2) ≤ (if (α && β) then p1 else 1 - p1) * (if (α || β) then p2 else 1 - p2) := by
-- proof
  apply StatMech.FK.edgeFactor_cross G p1 p2 hle α β

/--
[edgeProduct_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma edgeProduct_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2) :
-- imply
  edgeProduct G p1 a * edgeProduct G p2 b ≤ edgeProduct G p1 (a ⊓ b) * edgeProduct G p2 (a ⊔ b) := by
-- proof
  apply StatMech.FK.edgeProduct_cross G hp1 hp1' hp2 hp2' hle a b

/--
[fkWeight_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma fkWeight_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2)
  (hq : 1 ≤ q) :
-- imply
  fkWeight G p1 q a * fkWeight G p2 q b ≤ fkWeight G p1 q (a ⊓ b) * fkWeight G p2 q (a ⊔ b) := by
-- proof
  apply StatMech.FK.fkWeight_cross G hp1 hp1' hp2 hp2' hle hq a b

/--
[fkProb_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma fkProb_cross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2)
  (hq : 1 ≤ q) :
-- imply
  fkProb G p1 q a * fkProb G p2 q b ≤ fkProb G p1 q (a ⊓ b) * fkProb G p2 q (a ⊔ b) := by
-- proof
  apply StatMech.FK.fkProb_cross G hp1 hp1' hp2 hp2' hle hq a b

/--
[fkProb_stochastically_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Comparison.lean)
-/
@[path]
private lemma fkProb_stochastically_increasing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p1 p2 q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp1 : 0 < p1)
  (hp1' : p1 < 1)
  (hp2 : 0 < p2)
  (hp2' : p2 < 1)
  (hle : p1 ≤ p2)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p1 q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p2 q ω := by
-- proof
  apply StatMech.FK.fkProb_stochastically_increasing G hp1 hp1' hp2 hp2' hle hq hA


-- created on 2026-10-23
