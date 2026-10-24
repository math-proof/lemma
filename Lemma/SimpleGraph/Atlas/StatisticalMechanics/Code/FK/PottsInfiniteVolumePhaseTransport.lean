import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PottsInfiniteVolumePhaseTransport
open MeasureTheory Filter Topology StatMech StatMech.FK


/--
[pottsColorEvent_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma pottsColorEvent_isClopen_eq
  {d q : Nat}
  {x : Site d}
  {b : Fin q} :
-- imply
  IsClopen (pottsColorEvent d q x b) := by
-- proof
  apply StatMech.FK.pottsColorEvent_isClopen d q x b

/--
[wiredPottsFiniteMeasure_real_pottsColorEvent_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma wiredPottsFiniteMeasure_real_pottsColorEvent_origin_eq
  {d n q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real} :
-- imply
  ((wiredPottsFiniteMeasure d n q b beta J : ProbabilityMeasure (PottsConfig d q)) : Measure (PottsConfig d q)).real (pottsColorEvent d q (origin d) b) = pottsBoundaryProbWired (boxGraph d n) (boxBoundary d n) q b beta J (boxOrigin d n) := by
-- proof
  apply StatMech.FK.wiredPottsFiniteMeasure_real_pottsColorEvent_origin d n q b beta J

/--
[wiredPottsFiniteMeasure_colorBias_eq_boundaryConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma wiredPottsFiniteMeasure_colorBias_eq_boundaryConnection_eq
  {d n q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hJ : 0 < J) :
-- imply
  ((wiredPottsFiniteMeasure d n q b beta J : ProbabilityMeasure (PottsConfig d q)) : Measure (PottsConfig d q)).real (pottsColorEvent d q (origin d) b) - 1 / (q : Real) = ((q : Real) - 1) / q * ((wiredFiniteMeasure d n (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.wiredPottsFiniteMeasure_colorBias_eq_boundaryConnection d n q hd hn hq b beta J hbeta hJ

/--
[wiredPottsLimit_colorBias_eq_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma wiredPottsLimit_colorBias_eq_fkTheta_eq
  {d q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
  {mu : ProbabilityMeasure (PottsConfig d q)}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hJ : 0 < J)
  (phi : Nat -> Nat)
  (hphi : StrictMono phi)
  (hmu : Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J) atTop (nhds mu)) :
-- imply
  ((mu : Measure (PottsConfig d q)).real (pottsColorEvent d q (origin d) b)) - 1 / (q : Real) = ((q : Real) - 1) / q * fkTheta d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q) := by
-- proof
  apply StatMech.FK.wiredPottsLimit_colorBias_eq_fkTheta d q hd hq b beta J hbeta hJ mu phi hphi hmu

/--
[Potts.monoIndicator_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma monoIndicator_relabel_eq
  {q : Nat}
  {e : Fin q ≃ Fin q}
  {edge : Sym2 V}
-- given
  (sigma : V -> Fin q) :
-- imply
  Potts.monoIndicator (fun x => e (sigma x)) edge = Potts.monoIndicator sigma edge := by
-- proof
  apply StatMech.FK.Potts.monoIndicator_relabel e sigma edge

/--
[Potts.pottsProb_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma pottsProb_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : Nat}
  [NeZero q]
  {e : Fin q ≃ Fin q}
  {beta J : Real}
-- given
  (sigma : V -> Fin q) :
-- imply
  Potts.pottsProb G q beta J (fun x => e (sigma x)) = Potts.pottsProb G q beta J sigma := by
-- proof
  apply StatMech.FK.Potts.pottsProb_relabel G e beta J sigma

/--
[pottsProbWired_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma pottsProbWired_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {e : Fin q ≃ Fin q}
  {beta J : Real}
-- given
  (bdry : V -> Prop)
  (he : e b = b)
  (sigma : V -> Fin q) :
-- imply
  pottsProbWired G bdry q b beta J (fun x => e (sigma x)) = pottsProbWired G bdry q b beta J sigma := by
-- proof
  apply StatMech.FK.pottsProbWired_relabel G bdry b e he beta J sigma

/--
[pottsColorProbWired_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma pottsColorProbWired_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  {b : Fin q}
  {beta J : Real}
  {x : V}
-- given
  (bdry : V -> Prop) :
-- imply
  pottsColorProbWired G bdry q b b beta J x = pottsBoundaryProbWired G bdry q b beta J x := by
-- proof
  apply StatMech.FK.pottsColorProbWired_self G bdry q b beta J x

/--
[pottsColorProbWired_eq_of_ne_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma pottsColorProbWired_eq_of_ne_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b a c : Fin q}
  {beta J : Real}
  {x : V}
-- given
  (bdry : V -> Prop)
  (ha : a ≠ b)
  (hc : c ≠ b) :
-- imply
  pottsColorProbWired G bdry q b a beta J x = pottsColorProbWired G bdry q b c beta J x := by
-- proof
  apply StatMech.FK.pottsColorProbWired_eq_of_ne_boundary G bdry q b a c beta J x ha hc

/--
[sum_pottsColorProbWired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma sum_pottsColorProbWired_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
  {x : V}
-- given
  (bdry : V -> Prop) :
-- imply
  ∑ a : Fin q, pottsColorProbWired G bdry q b a beta J x = 1 := by
-- proof
  apply StatMech.FK.sum_pottsColorProbWired G bdry q b beta J x

/--
[pottsColorProbWired_other_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma pottsColorProbWired_other_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b a : Fin q}
  {beta J : Real}
  {x : V}
-- given
  (bdry : V -> Prop)
  (hq : 2 <= q)
  (ha : a ≠ b) :
-- imply
  pottsColorProbWired G bdry q b a beta J x = (1 - pottsBoundaryProbWired G bdry q b beta J x) / ((q : Real) - 1) := by
-- proof
  apply StatMech.FK.pottsColorProbWired_other_eq G bdry q hq b a ha beta J x

/--
[wiredPottsFiniteMeasure_real_pottsColorEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma wiredPottsFiniteMeasure_real_pottsColorEvent_eq
  {d n q : Nat}
  [NeZero q]
  {b a : Fin q}
  {beta J : Real} :
-- imply
  ((wiredPottsFiniteMeasure d n q b beta J : ProbabilityMeasure (PottsConfig d q)) : Measure (PottsConfig d q)).real (pottsColorEvent d q (origin d) a) = pottsColorProbWired (boxGraph d n) (boxBoundary d n) q b a beta J (boxOrigin d n) := by
-- proof
  apply StatMech.FK.wiredPottsFiniteMeasure_real_pottsColorEvent d n q b a beta J

/--
[wiredPottsLimit_otherColorBias_eq_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma wiredPottsLimit_otherColorBias_eq_fkTheta_eq
  {d q : Nat}
  [NeZero q]
  {b a : Fin q}
  {beta J : Real}
  {mu : ProbabilityMeasure (PottsConfig d q)}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (ha : a ≠ b)
  (hbeta : 0 < beta)
  (hJ : 0 < J)
  (phi : Nat -> Nat)
  (hphi : StrictMono phi)
  (hmu : Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J) atTop (nhds mu)) :
-- imply
  ((mu : Measure (PottsConfig d q)).real (pottsColorEvent d q (origin d) a)) - 1 / (q : Real) = -(1 / (q : Real)) * fkTheta d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q) := by
-- proof
  apply StatMech.FK.wiredPottsLimit_otherColorBias_eq_fkTheta d q hd hq b a ha beta J hbeta hJ mu phi hphi hmu

/--
[Potts.pottsColorProbability_eq_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma pottsColorProbability_eq_inv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : Nat}
  [NeZero q]
  {beta J : Real}
  {x : V}
  {b : Fin q} :
-- imply
  (∑ sigma : V -> Fin q, Potts.pottsProb G q beta J sigma * (if sigma x = b then 1 else 0)) = 1 / (q : Real) := by
-- proof
  apply StatMech.FK.Potts.pottsColorProbability_eq_inv G q beta J x b

/--
[freePottsFiniteMeasure_real_pottsColorEvent_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma freePottsFiniteMeasure_real_pottsColorEvent_origin_eq
  {d n q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real} :
-- imply
  ((freePottsFiniteMeasure d n q beta J : ProbabilityMeasure (PottsConfig d q)) : Measure (PottsConfig d q)).real (pottsColorEvent d q (origin d) b) = 1 / (q : Real) := by
-- proof
  apply StatMech.FK.freePottsFiniteMeasure_real_pottsColorEvent_origin d n q b beta J

/--
[freePottsLimit_colorProbability_eq_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma freePottsLimit_colorProbability_eq_inv_eq
  {d q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
  {mu : ProbabilityMeasure (PottsConfig d q)}
-- given
  (phi : Nat -> Nat)
  (hmu : Tendsto (fun n => freePottsFiniteMeasure d (phi n) q beta J) atTop (nhds mu)) :
-- imply
  (mu : Measure (PottsConfig d q)).real (pottsColorEvent d q (origin d) b) = 1 / (q : Real) := by
-- proof
  apply StatMech.FK.freePottsLimit_colorProbability_eq_inv d q b beta J mu phi hmu

/--
[freePottsLimit_ne_wiredPottsLimit_of_fkTheta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma freePottsLimit_ne_wiredPottsLimit_of_fkTheta_pos_eq
  {d q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
  {muFree muWired : ProbabilityMeasure (PottsConfig d q)}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hJ : 0 < J)
  (phiFree phiWired : Nat -> Nat)
  (hphiWired : StrictMono phiWired)
  (hmuFree : Tendsto (fun n => freePottsFiniteMeasure d (phiFree n) q beta J) atTop (nhds muFree))
  (hmuWired : Tendsto (fun n => wiredPottsFiniteMeasure d (phiWired n) q b beta J) atTop (nhds muWired))
  (htheta : 0 < fkTheta d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q)) :
-- imply
  muFree ≠ muWired := by
-- proof
  apply StatMech.FK.freePottsLimit_ne_wiredPottsLimit_of_fkTheta_pos d q hd hq b beta J hbeta hJ muFree muWired phiFree phiWired hphiWired hmuFree hmuWired htheta

/--
[wiredPottsLimits_ne_of_boundary_ne_of_fkTheta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma wiredPottsLimits_ne_of_boundary_ne_of_fkTheta_pos_eq
  {d q : Nat}
  [NeZero q]
  {b c : Fin q}
  {beta J : Real}
  {muB muC : ProbabilityMeasure (PottsConfig d q)}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (hbc : b ≠ c)
  (hbeta : 0 < beta)
  (hJ : 0 < J)
  (phiB phiC : Nat -> Nat)
  (hphiB : StrictMono phiB)
  (hphiC : StrictMono phiC)
  (hmuB : Tendsto (fun n => wiredPottsFiniteMeasure d (phiB n) q b beta J) atTop (nhds muB))
  (hmuC : Tendsto (fun n => wiredPottsFiniteMeasure d (phiC n) q c beta J) atTop (nhds muC))
  (htheta : 0 < fkTheta d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q)) :
-- imply
  muB ≠ muC := by
-- proof
  apply StatMech.FK.wiredPottsLimits_ne_of_boundary_ne_of_fkTheta_pos d q hd hq b c hbc beta J hbeta hJ muB muC phiB phiC hphiB hphiC hmuB hmuC htheta

/--
[wiredPottsOrderedInfiniteVolume_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean)
-/
@[path]
private lemma wiredPottsOrderedInfiniteVolume_exists_eq
  {d q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hJ : 0 < J) :
-- imply
  ∃ (Xi : ProbabilityMeasure (PottsJointConfig d q)) (mu : ProbabilityMeasure (PottsConfig d q)) (phi : Nat -> Nat), StrictMono phi ∧ Tendsto (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J (by apply sub_nonneg.mpr rw [Real.exp_le_one_iff] exact neg_nonpos.mpr (mul_pos hbeta hJ).le)) atTop (nhds Xi) ∧ Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J) atTop (nhds mu) ∧ Xi.map continuous_fst.measurable.aemeasurable = mu ∧ Xi.map continuous_snd.measurable.aemeasurable = wiredInfiniteVolume d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) ∧ (mu : Measure (PottsConfig d q)).real (pottsColorEvent d q (origin d) b) - 1 / (q : Real) = ((q : Real) - 1) / q * fkTheta d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) (q := q) := by
-- proof
  apply StatMech.FK.wiredPottsOrderedInfiniteVolume_exists d q hd hq b beta J hbeta hJ


-- created on 2026-10-23
