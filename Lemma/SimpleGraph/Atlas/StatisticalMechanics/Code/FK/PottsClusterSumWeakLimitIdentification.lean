import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification
open Filter MeasureTheory Set Topology StatMech StatMech.FK


/--
[freeClusterColorJointPMF_eq_ivp_freeJointPMF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma freeClusterColorJointPMF_eq_ivp_freeJointPMF_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : Nat}
  [NeZero q]
  {p : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < (q : Real)) :
-- imply
  freeClusterColorJointPMF G q hp hp1 hq = ivp_freeJointPMF G q hp hp1 hq := by
-- proof
  apply StatMech.FK.freeClusterColorJointPMF_eq_ivp_freeJointPMF G q hp hp1 hq

/--
[finiteOpenComponentSums_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma finiteOpenComponentSums_law_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : Nat}
  [NeZero q]
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  Measure.map (finiteOpenComponentSums G omega) (PMF.uniformOfFintype (V -> Fin q)).toMeasure = (PMF.uniformOfFintype ((openSub G omega).ConnectedComponent -> Fin q)).toMeasure := by
-- proof
  apply StatMech.FK.finiteOpenComponentSums_law G q omega

/--
[finiteOpenComponentSums_pmf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma finiteOpenComponentSums_pmf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : Nat}
  [NeZero q]
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  (PMF.uniformOfFintype (V -> Fin q)).map (finiteOpenComponentSums G omega) = PMF.uniformOfFintype ((openSub G omega).ConnectedComponent -> Fin q) := by
-- proof
  apply StatMech.FK.finiteOpenComponentSums_pmf G q omega

/--
[freeSiteClusterSumJointPMF_eq_ivp_freeJointPMF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma freeSiteClusterSumJointPMF_eq_ivp_freeJointPMF_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : Nat}
  [NeZero q]
  {p : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < (q : Real)) :
-- imply
  (fkPMF G hp hp1 hq).bind (fun omega => (PMF.uniformOfFintype (V -> Fin q)).map fun label => (IsingFK.coloring G omega (finiteOpenComponentSums G omega label), omega)) = ivp_freeJointPMF G q hp hp1 hq := by
-- proof
  apply StatMech.FK.freeSiteClusterSumJointPMF_eq_ivp_freeJointPMF G q hp hp1 hq

/--
[finiteOpenComponentRepresentative_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma finiteOpenComponentRepresentative_component_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega : ConfigSpace (Sym2 V)}
  {C : (openSub G omega).ConnectedComponent} :
-- imply
  (openSub G omega).connectedComponentMk (finiteOpenComponentRepresentative G omega C) = C := by
-- proof
  apply StatMech.FK.finiteOpenComponentRepresentative_component G omega C

/--
[measurable_pottsBoxJointRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma measurable_pottsBoxJointRestrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : Nat} :
-- imply
  Measurable (pottsBoxJointRestrict d n q) := by
-- proof
  apply StatMech.FK.measurable_pottsBoxJointRestrict G d n q

/--
[continuous_pottsBoxJointRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma continuous_pottsBoxJointRestrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : Nat} :
-- imply
  Continuous (pottsBoxJointRestrict d n q) := by
-- proof
  apply StatMech.FK.continuous_pottsBoxJointRestrict G d n q

/--
[boxClusterSumSpin_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma boxClusterSumSpin_law_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  Measure.map (fun label (x : boxVerts d n) => pottsClusterSumSpin boundaryColor (extendEdge d n omega) label (x : Site d)) (pottsIIDLabelMeasure d q) = ((PMF.uniformOfFintype ((openSub (boxGraph d n) omega).ConnectedComponent -> Fin q)).map (IsingFK.coloring (boxGraph d n) omega)).toMeasure := by
-- proof
  apply StatMech.FK.boxClusterSumSpin_law G boundaryColor n omega

/--
[measurable_boxClusterSumJointFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma measurable_boxClusterSumJointFactor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {n : Nat} :
-- imply
  Measurable (boxClusterSumJointFactor (d := d) boundaryColor n) := by
-- proof
  apply StatMech.FK.measurable_boxClusterSumJointFactor G boundaryColor n

/--
[pottsBoxJointRestrict_clusterFactor_extendEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma pottsBoxJointRestrict_clusterFactor_extendEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {n : Nat}
-- given
  (input : ConfigSpace (Sym2 (boxVerts d n)) × (Site d -> Fin q)) :
-- imply
  pottsBoxJointRestrict d n q (pottsClusterSumJointFactor boundaryColor (extendEdge d n input.1, input.2)) = boxClusterSumJointFactor boundaryColor n input := by
-- proof
  apply StatMech.FK.pottsBoxJointRestrict_clusterFactor_extendEdge G boundaryColor n input

/--
[freePottsJointFiniteMeasure_map_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma freePottsJointFiniteMeasure_map_boxRestrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : Nat}
  [NeZero q]
  {beta J : Real}
-- given
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
-- imply
  (freePottsJointFiniteMeasure d n q beta J hp hp1).map (measurable_pottsBoxJointRestrict d n q).aemeasurable = ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1 (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : Real) < q)).toMeasure, inferInstance⟩ := by
-- proof
  apply StatMech.FK.freePottsJointFiniteMeasure_map_boxRestrict G d n q beta J hp hp1

/--
[freeESJointFiniteMeasure_map_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma freeESJointFiniteMeasure_map_boxRestrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : Nat}
  [NeZero q]
  {p : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < (q : Real)) :
-- imply
  (freeESJointFiniteMeasure d n q hp hp1 hq).map (measurable_pottsBoxJointRestrict d n q).aemeasurable = ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure, inferInstance⟩ := by
-- proof
  apply StatMech.FK.freeESJointFiniteMeasure_map_boxRestrict G d n q hp hp1 hq

/--
[pottsClusterSumJointProbabilityMeasure_freeFinite_map_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma pottsClusterSumJointProbabilityMeasure_freeFinite_map_boxRestrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {n : Nat}
  {p : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < (q : Real)) :
-- imply
  (pottsClusterSumJointProbabilityMeasure boundaryColor (freeFiniteMeasure d n hp hp1 hq)).map (measurable_pottsBoxJointRestrict d n q).aemeasurable = ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure, inferInstance⟩ := by
-- proof
  apply StatMech.FK.pottsClusterSumJointProbabilityMeasure_freeFinite_map_boxRestrict G boundaryColor n hp hp1 hq

/--
[isClopen_pottsSpinCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma isClopen_pottsSpinCylinder_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : Nat}
  {s : Finset (Site d)}
-- given
  (S : Set (∀ _x : s, Fin q)) :
-- imply
  IsClopen (cylinder (α := fun _ : Site d => Fin q) s S) := by
-- proof
  apply StatMech.FK.isClopen_pottsSpinCylinder G s S

/--
[isClopen_pottsJointCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma isClopen_pottsJointCylinder_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : Nat}
  {spinSites : Finset (Site d)}
  {edgeSites : Finset (Sym2 (Site d))}
-- given
  (spinSet : Set (∀ _x : spinSites, Fin q))
  (edgeSet : Set (∀ _e : edgeSites, Bool)) :
-- imply
  IsClopen (pottsJointCylinder spinSites spinSet edgeSites edgeSet) := by
-- proof
  apply StatMech.FK.isClopen_pottsJointCylinder G spinSites spinSet edgeSites edgeSet

/--
[eventually_freeESJoint_eq_clusterSum_on_pottsJointCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma eventually_freeESJoint_eq_clusterSum_on_pottsJointCylinder_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {p : Real}
  {spinSites : Finset (Site d)}
  {edgeSites : Finset (Sym2 (Site d))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < (q : Real))
  (phi : Nat -> Nat)
  (hphi : StrictMono phi)
  (spinSet : Set (∀ _x : spinSites, Fin q))
  (edgeSet : Set (∀ _e : edgeSites, Bool)) :
-- imply
  Filter.EventuallyEq atTop (fun k => pottsClusterSumJointProbabilityMeasure boundaryColor (freeFiniteMeasure d (phi k) hp hp1 hq) (pottsJointCylinder spinSites spinSet edgeSites edgeSet)) (fun k => freeESJointFiniteMeasure d (phi k) q hp hp1 hq (pottsJointCylinder spinSites spinSet edgeSites edgeSet)) := by
-- proof
  apply StatMech.FK.eventually_freeESJoint_eq_clusterSum_on_pottsJointCylinder G boundaryColor hp hp1 hq phi hphi spinSites spinSet edgeSites edgeSet

/--
[ProbabilityMeasure.ext_of_pottsJointCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma ext_of_pottsJointCylinder_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : Nat}
  {mu nu : ProbabilityMeasure (PottsJointConfig d q)}
-- given
  (h : ∀ (spinSites : Finset (Site d)) (spinSet : Set (∀ _x : spinSites, Fin q)) (edgeSites : Finset (Sym2 (Site d))) (edgeSet : Set (∀ _e : edgeSites, Bool)), mu (pottsJointCylinder spinSites spinSet edgeSites edgeSet) = nu (pottsJointCylinder spinSites spinSet edgeSites edgeSet)) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FK.ProbabilityMeasure.ext_of_pottsJointCylinder G mu nu h

/--
[freeESJointWeakLimit_eq_clusterSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma freeESJointWeakLimit_eq_clusterSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {p : Real}
  {Xi : ProbabilityMeasure (PottsJointConfig d q)}
  {edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < (q : Real))
  (phi : Nat -> Nat)
  (hphi : StrictMono phi)
  (hjoint : Tendsto (fun k => freeESJointFiniteMeasure d (phi k) q hp hp1 hq) atTop (nhds Xi))
  (hedge : Tendsto (fun k => freeFiniteMeasure d (phi k) hp hp1 hq) atTop (nhds edgeLimit))
  (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _), omega ∈ pottsAllClustersFiniteEvent d) :
-- imply
  Xi = pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit := by
-- proof
  apply StatMech.FK.freeESJointWeakLimit_eq_clusterSum G boundaryColor hp hp1 hq phi hphi Xi edgeLimit hjoint hedge hfinite

/--
[freePottsJointWeakLimit_eq_clusterSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean)
-/
@[path]
private lemma freePottsJointWeakLimit_eq_clusterSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {beta J : Real}
  {Xi : ProbabilityMeasure (PottsJointConfig d q)}
  {edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1)
  (hq : 0 < (q : Real))
  (phi : Nat -> Nat)
  (hphi : StrictMono phi)
  (hjoint : Tendsto (fun k => freePottsJointFiniteMeasure d (phi k) q beta J hp hp1) atTop (nhds Xi))
  (hedge : Tendsto (fun k => freeFiniteMeasure d (phi k) hp hp1 hq) atTop (nhds edgeLimit))
  (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _), omega ∈ pottsAllClustersFiniteEvent d) :
-- imply
  Xi = pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit := by
-- proof
  apply StatMech.FK.freePottsJointWeakLimit_eq_clusterSum G boundaryColor beta J hp hp1 hq phi hphi Xi edgeLimit hjoint hedge hfinite


-- created on 2026-10-23
