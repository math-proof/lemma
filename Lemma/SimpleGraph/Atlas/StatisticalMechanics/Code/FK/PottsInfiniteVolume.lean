import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PottsInfiniteVolume
open MeasureTheory Filter Topology TopologicalSpace StatMech StatMech.FK StatMech.FK.Wired


/--
[probabilityMeasure_seq_compact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma probabilityMeasure_seq_compact_eq
  [TopologicalSpace X]
  [MeasurableSpace X]
  [BorelSpace X]
  [CompactSpace X]
  [SecondCountableTopology X]
  [T2Space X]
  {mu : ℕ → ProbabilityMeasure X} :
-- imply
  ∃ (nu : ProbabilityMeasure X) (phi : ℕ → ℕ), StrictMono phi ∧ Tendsto (mu ∘ phi) atTop (nhds nu) := by
-- proof
  apply StatMech.FK.probabilityMeasure_seq_compact mu

/--
[ivp_freeJointProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_freeJointProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {z : (V → Fin q) × ConfigSpace (Sym2 V)}
-- given
  (hp : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ ivp_freeJointProb G q p z := by
-- proof
  apply StatMech.FK.ivp_freeJointProb_nonneg G hp hp1 z

/--
[ivp_freeJointProb_eq_fkProb_div_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_freeJointProb_eq_fkProb_div_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : Nat}
  {p : Real}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hq : 0 < (q : Real))
  (sigma : V -> Fin q) :
-- imply
  ivp_freeJointProb G q p (sigma, omega) = if ConstOnOpen G omega sigma then fkProb G p (q : Real) omega / (q : Real) ^ numClusters G omega else 0 := by
-- proof
  apply StatMech.FK.ivp_freeJointProb_eq_fkProb_div_pow G hq sigma omega

/--
[ivp_freeJointProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_freeJointProb_sum_eq_one_eq
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
  ∑ z : (V → Fin q) × ConfigSpace (Sym2 V), ivp_freeJointProb G q p z = 1 := by
-- proof
  apply StatMech.FK.ivp_freeJointProb_sum_eq_one G hp hp1 hq

/--
[ivp_freeJointPMF_map_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_freeJointPMF_map_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {beta J : ℝ}
-- given
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
-- imply
  (ivp_freeJointPMF G q hp hp1 (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).map Prod.fst = Potts.pottsPMF G q beta J := by
-- proof
  apply StatMech.FK.ivp_freeJointPMF_map_fst G q beta J hp hp1

/--
[ivp_freeJointPMF_map_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_freeJointPMF_map_snd_eq
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
  (ivp_freeJointPMF G q hp hp1 hq).map Prod.snd = fkPMF G hp hp1 hq := by
-- proof
  apply StatMech.FK.ivp_freeJointPMF_map_snd G q p hp hp1 hq

/--
[ivp_esZWired_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_esZWired_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {beta J : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  0 < esZWired G bdry q b (1 - Real.exp (-(beta * J))) := by
-- proof
  apply StatMech.FK.Wired.ivp_esZWired_pos G bdry b beta J

/--
[ivp_wiredJointProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_wiredJointProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {beta J : ℝ}
  {z : (V → Fin q) × ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
-- imply
  0 ≤ ivp_wiredJointProb G bdry b beta J z := by
-- proof
  apply StatMech.FK.Wired.ivp_wiredJointProb_nonneg G bdry b beta J hp z

/--
[ivp_wiredJointProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_wiredJointProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {beta J : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  ∑ z : (V → Fin q) × ConfigSpace (Sym2 V), ivp_wiredJointProb G bdry b beta J z = 1 := by
-- proof
  apply StatMech.FK.Wired.ivp_wiredJointProb_sum_eq_one G bdry b beta J

/--
[ivp_wiredJointPMF_map_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_wiredJointPMF_map_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {beta J : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
-- imply
  (ivp_wiredJointPMF G bdry b beta J hp).map Prod.fst = PMF.ofFintype (fun s => ENNReal.ofReal (pottsProbWired G bdry q b beta J s)) (by rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => pottsProbWired_nonneg G bdry q b beta J s), pottsProbWired_sum_eq_one G bdry q b beta J, ENNReal.ofReal_one]) := by
-- proof
  apply StatMech.FK.Wired.ivp_wiredJointPMF_map_fst G bdry b beta J hp

/--
[ivp_wiredJointPMF_map_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_wiredJointPMF_map_snd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℕ}
  [NeZero q]
  {b : Fin q}
  {beta J : ℝ}
  {v0 : V}
-- given
  (bdry : V → Prop)
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1)
  (hv0 : bdry v0) :
-- imply
  (ivp_wiredJointPMF G bdry b beta J hp.le).map Prod.snd = wiredFkPMF G bdry hp hp1 (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q) := by
-- proof
  apply StatMech.FK.Wired.ivp_wiredJointPMF_map_snd G bdry b beta J hp hp1 v0 hv0

/--
[ivp_measurable_extendSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_measurable_extendSpin_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : ℕ}
  [NeZero q] :
-- imply
  Measurable (ivp_extendSpin d n q) := by
-- proof
  apply StatMech.FK.ivp_measurable_extendSpin G d n q

/--
[ivp_measurable_extendJoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma ivp_measurable_extendJoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : ℕ}
  [NeZero q] :
-- imply
  Measurable (ivp_extendJoint d n q) := by
-- proof
  apply StatMech.FK.ivp_measurable_extendJoint G d n q

/--
[freePottsJointFiniteMeasure_map_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma freePottsJointFiniteMeasure_map_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : ℕ}
  [NeZero q]
  {beta J : ℝ}
-- given
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
-- imply
  (freePottsJointFiniteMeasure d n q beta J hp hp1).map continuous_fst.measurable.aemeasurable = freePottsFiniteMeasure d n q beta J := by
-- proof
  apply StatMech.FK.freePottsJointFiniteMeasure_map_fst G d n q beta J hp hp1

/--
[freePottsJointFiniteMeasure_map_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma freePottsJointFiniteMeasure_map_snd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : ℕ}
  [NeZero q]
  {beta J : ℝ}
-- given
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
-- imply
  (freePottsJointFiniteMeasure d n q beta J hp hp1).map continuous_snd.measurable.aemeasurable = freeFiniteMeasure d n hp hp1 (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q) := by
-- proof
  apply StatMech.FK.freePottsJointFiniteMeasure_map_snd G d n q beta J hp hp1

/--
[wiredPottsJointFiniteMeasure_map_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma wiredPottsJointFiniteMeasure_map_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : ℕ}
  [NeZero q]
  {b : Fin q}
  {beta J : ℝ}
-- given
  (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
-- imply
  (wiredPottsJointFiniteMeasure d n q b beta J hp).map continuous_fst.measurable.aemeasurable = wiredPottsFiniteMeasure d n q b beta J := by
-- proof
  apply StatMech.FK.wiredPottsJointFiniteMeasure_map_fst G d n q b beta J hp

/--
[wiredPottsJointFiniteMeasure_map_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma wiredPottsJointFiniteMeasure_map_snd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : ℕ}
  [NeZero q]
  {b : Fin q}
  {beta J : ℝ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
-- imply
  (wiredPottsJointFiniteMeasure d n q b beta J hp.le).map continuous_snd.measurable.aemeasurable = wiredFiniteMeasure d n hp hp1 (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q) := by
-- proof
  apply StatMech.FK.wiredPottsJointFiniteMeasure_map_snd G d n q hd hn b beta J hp hp1

/--
[freePottsInfiniteVolume_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma freePottsInfiniteVolume_exists_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : ℕ}
  [NeZero q]
  {beta J : ℝ}
-- given
  (hq : 2 ≤ q)
  (hbeta : 0 < beta)
  (hJ : 0 < J) :
-- imply
  ∃ (Xi : ProbabilityMeasure (PottsJointConfig d q)) (mu : ProbabilityMeasure (PottsConfig d q)) (phi : ℕ → ℕ), StrictMono phi ∧ Tendsto (fun n => freePottsJointFiniteMeasure d (phi n) q beta J (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by have he := Real.exp_pos (-(beta * J)) linarith)) atTop (nhds Xi) ∧ Tendsto (fun n => freePottsFiniteMeasure d (phi n) q beta J) atTop (nhds mu) ∧ Xi.map continuous_fst.measurable.aemeasurable = mu ∧ Xi.map continuous_snd.measurable.aemeasurable = freeInfiniteVolume d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by have he := Real.exp_pos (-(beta * J)) linarith) (by exact_mod_cast (show 0 < q by omega) : (0 : ℝ) < q) := by
-- proof
  apply StatMech.FK.freePottsInfiniteVolume_exists G d q hq beta J hbeta hJ

/--
[wiredPottsInfiniteVolume_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean)
-/
@[path]
private lemma wiredPottsInfiniteVolume_exists_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : ℕ}
  [NeZero q]
  {b : Fin q}
  {beta J : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 2 ≤ q)
  (hbeta : 0 < beta)
  (hJ : 0 < J) :
-- imply
  ∃ (Xi : ProbabilityMeasure (PottsJointConfig d q)) (mu : ProbabilityMeasure (PottsConfig d q)) (phi : ℕ → ℕ), StrictMono phi ∧ Tendsto (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J (by apply sub_nonneg.mpr rw [Real.exp_le_one_iff] exact neg_nonpos.mpr (mul_pos hbeta hJ).le)) atTop (nhds Xi) ∧ Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J) atTop (nhds mu) ∧ Xi.map continuous_fst.measurable.aemeasurable = mu ∧ Xi.map continuous_snd.measurable.aemeasurable = wiredInfiniteVolume d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by have he := Real.exp_pos (-(beta * J)) linarith) (by exact_mod_cast (show 0 < q by omega) : (0 : ℝ) < q) := by
-- proof
  apply StatMech.FK.wiredPottsInfiniteVolume_exists G d q hd hq b beta J hbeta hJ


-- created on 2026-10-23
