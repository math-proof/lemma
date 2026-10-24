import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PottsClusterSumWiredLimit
open Filter MeasureTheory Set Topology StatMech StatMech.FK


/--
[pottsClusterSumJointProbabilityMeasure_wiredOpenExterior_map_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredLimit.lean)
-/
@[path]
private lemma pottsClusterSumJointProbabilityMeasure_wiredOpenExterior_map_boxRestrict_eq
  {d q : Nat}
  [NeZero q]
  {n : Nat}
  {boundaryColor : Fin q}
  {beta J : Real}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n)
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1)
  (hq : 0 < (q : Real)) :
-- imply
  (pottsClusterSumJointProbabilityMeasure boundaryColor (wiredOpenExteriorFiniteMeasure d n hp hp1 hq)).map (measurable_pottsBoxJointRestrict d n q).aemeasurable = ⟨(Wired.clusterColorJointPMF (boxGraph d n) (boxBoundary d n) boundaryColor beta J hp hp1).toMeasure, inferInstance⟩ := by
-- proof
  apply StatMech.FK.pottsClusterSumJointProbabilityMeasure_wiredOpenExterior_map_boxRestrict hd n hn boundaryColor beta J hp hp1 hq

/--
[eventually_wiredPottsJoint_eq_openExteriorClusterSum_on_pottsJointCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredLimit.lean)
-/
@[path]
private lemma eventually_wiredPottsJoint_eq_openExteriorClusterSum_on_pottsJointCylinder_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {beta J : Real}
  {phi : Nat → Nat}
  {spinSites : Finset (Site d)}
  {edgeSites : Finset (Sym2 (Site d))}
-- given
  (hd : 2 ≤ d)
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1)
  (hq : 0 < (q : Real))
  (hphi : StrictMono phi)
  (hphiPos : ∀ k, 1 ≤ phi k)
  (spinSet : Set (∀ _x : spinSites, Fin q))
  (edgeSet : Set (∀ _e : edgeSites, Bool)) :
-- imply
  Filter.EventuallyEq atTop (fun k => pottsClusterSumJointProbabilityMeasure boundaryColor (wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq) (pottsJointCylinder spinSites spinSet edgeSites edgeSet)) (fun k => wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le (pottsJointCylinder spinSites spinSet edgeSites edgeSet)) := by
-- proof
  apply StatMech.FK.eventually_wiredPottsJoint_eq_openExteriorClusterSum_on_pottsJointCylinder hd boundaryColor beta J hp hp1 hq phi hphi hphiPos spinSites spinSet edgeSites edgeSet

/--
[wiredPottsJointWeakLimit_spinMarginal_eq_clusterSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredLimit.lean)
-/
@[path]
private lemma wiredPottsJointWeakLimit_spinMarginal_eq_clusterSum_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {beta J : Real}
  {Xi : ProbabilityMeasure (PottsJointConfig d q)}
-- given
  (hd : 2 ≤ d)
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1)
  (hq : 1 ≤ (q : Real))
  (phi : Nat -> Nat)
  (hphi : StrictMono phi)
  (hphiPos : ∀ k, 1 ≤ phi k)
  (hjoint : Tendsto (fun k => wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le) atTop (nhds Xi))
  (hedge : Tendsto (fun k => wiredFiniteMeasure d (phi k) hp hp1 (zero_lt_one.trans_le hq)) atTop (nhds (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)))) :
-- imply
  Xi.map continuous_fst.measurable.aemeasurable = (pottsClusterSumJointProbabilityMeasure boundaryColor (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq))).map continuous_fst.measurable.aemeasurable := by
-- proof
  apply StatMech.FK.wiredPottsJointWeakLimit_spinMarginal_eq_clusterSum hd boundaryColor beta J hp hp1 hq phi hphi hphiPos Xi hjoint hedge

/--
[wiredPottsJointWeakLimit_eq_clusterSum_of_allClustersFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredLimit.lean)
-/
@[path]
private lemma wiredPottsJointWeakLimit_eq_clusterSum_of_allClustersFinite_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {beta J : Real}
  {phi : Nat → Nat}
  {Xi : ProbabilityMeasure (PottsJointConfig d q)}
  {edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hd : 2 ≤ d)
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1)
  (hq : 0 < (q : Real))
  (hphi : StrictMono phi)
  (hphiPos : ∀ k, 1 ≤ phi k)
  (hjoint : Tendsto (fun k => wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le) atTop (nhds Xi))
  (hedge : Tendsto (fun k => wiredFiniteMeasure d (phi k) hp hp1 hq) atTop (nhds edgeLimit))
  (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _), omega ∈ pottsAllClustersFiniteEvent d) :
-- imply
  Xi = pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit := by
-- proof
  apply StatMech.FK.wiredPottsJointWeakLimit_eq_clusterSum_of_allClustersFinite hd boundaryColor beta J hp hp1 hq phi hphi hphiPos Xi edgeLimit hjoint hedge hfinite

/--
[exists_wiredPottsFiniteMeasure_tendsto_clusterSumSpinMarginal_of_allClustersFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredLimit.lean)
-/
@[path]
private lemma exists_wiredPottsFiniteMeasure_tendsto_clusterSumSpinMarginal_of_allClustersFinite_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {beta J : Real}
-- given
  (hd : 2 ≤ d)
  (hq : 2 ≤ q)
  (hbeta : 0 < beta)
  (hJ : 0 < J)
  (hfinite : ∀ᵐ omega ∂((wiredInfiniteVolume d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _), omega ∈ pottsAllClustersFiniteEvent d) :
-- imply
  ∃ phi : Nat → Nat, StrictMono phi ∧ Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q boundaryColor beta J) atTop (nhds ((pottsClusterSumJointProbabilityMeasure boundaryColor (wiredInfiniteVolume d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q))).map continuous_fst.measurable.aemeasurable)) := by
-- proof
  apply StatMech.FK.exists_wiredPottsFiniteMeasure_tendsto_clusterSumSpinMarginal_of_allClustersFinite d q hd hq boundaryColor beta J hbeta hJ hfinite

/--
[exists_wiredPottsFiniteMeasure_tendsto_clusterSumSpinMarginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredLimit.lean)
-/
@[path]
private lemma exists_wiredPottsFiniteMeasure_tendsto_clusterSumSpinMarginal_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {beta J : Real}
-- given
  (hd : 2 ≤ d)
  (hq : 2 ≤ q)
  (hbeta : 0 < beta)
  (hJ : 0 < J) :
-- imply
  ∃ phi : Nat → Nat, StrictMono phi ∧ Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q boundaryColor beta J) atTop (nhds ((pottsClusterSumJointProbabilityMeasure boundaryColor (wiredInfiniteVolume d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q))).map continuous_fst.measurable.aemeasurable)) := by
-- proof
  apply StatMech.FK.exists_wiredPottsFiniteMeasure_tendsto_clusterSumSpinMarginal d q hd hq boundaryColor beta J hbeta hJ


-- created on 2026-10-23
