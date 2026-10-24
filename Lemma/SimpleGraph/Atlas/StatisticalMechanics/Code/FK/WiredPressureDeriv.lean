import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.WiredPressureDeriv
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[wpd_wiredFkZ_logistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredFkZ_logistic_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {t q : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  wiredFkZ G bdry (fsc_logistic t) q = ivp2_Ssum (fun ω => q ^ numClustersWired G bdry ω) (fun ω => (openCount G ω : ℝ)) t / (1 + Real.exp t) ^ G.edgeFinset.card := by
-- proof
  apply StatMech.FK.wpd_wiredFkZ_logistic G bdry t q

/--
[wpd_wiredTiltFreeEnergy_eq_Kcgf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredTiltFreeEnergy_eq_Kcgf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℝ}
  {t : ℝ}
-- given
  (bdry : V → Prop)
  (hq : 0 < q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  wpd_wiredTiltFreeEnergy G bdry q t = (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf (fun ω => q ^ numClustersWired G bdry ω) (fun ω => (openCount G ω : ℝ)) t := by
-- proof
  apply StatMech.FK.wpd_wiredTiltFreeEnergy_eq_Kcgf G bdry q hq hE t

/--
[wpd_wiredTiltFreeEnergy_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredTiltFreeEnergy_convexOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℝ}
-- given
  (bdry : V → Prop)
  (hq : 0 < q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  ConvexOn ℝ univ (wpd_wiredTiltFreeEnergy G bdry q) := by
-- proof
  apply StatMech.FK.wpd_wiredTiltFreeEnergy_convexOn G bdry q hq hE

/--
[wpd_wiredCgfMean_eq_openCount_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredCgfMean_eq_openCount_expect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℝ}
  {t : ℝ}
-- given
  (bdry : V → Prop)
  (hq : 0 < q) :
-- imply
  wpd_wiredFkExpect G bdry (fsc_logistic t) q (fun ω => (openCount G ω : ℝ)) = ivp2_S1 (fun ω => q ^ numClustersWired G bdry ω) (fun ω => (openCount G ω : ℝ)) t / ivp2_Ssum (fun ω => q ^ numClustersWired G bdry ω) (fun ω => (openCount G ω : ℝ)) t := by
-- proof
  apply StatMech.FK.wpd_wiredCgfMean_eq_openCount_expect G bdry q hq t

/--
[wpd_wiredTiltFreeEnergy_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredTiltFreeEnergy_hasDerivAt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℝ}
  {t : ℝ}
-- given
  (bdry : V → Prop)
  (hq : 0 < q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  HasDerivAt (wpd_wiredTiltFreeEnergy G bdry q) ((1 / (G.edgeFinset.card : ℝ)) * wpd_wiredFkExpect G bdry (fsc_logistic t) q (fun ω => (openCount G ω : ℝ))) t := by
-- proof
  apply StatMech.FK.wpd_wiredTiltFreeEnergy_hasDerivAt G bdry q hq hE t

/--
[wpd_wiredFkExpect_openCount_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredFkExpect_openCount_eq_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  wpd_wiredFkExpect G bdry p q (fun ω => (openCount G ω : ℝ)) = ∑ e ∈ G.edgeFinset, edgeMargProb (wiredFkProb G bdry p q) e := by
-- proof
  apply StatMech.FK.wpd_wiredFkExpect_openCount_eq_sum G bdry p q

/--
[wpd_avgWiredDensity_eq_sum_edgeMarg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_avgWiredDensity_eq_sum_edgeMarg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℝ}
  {t : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  wpd_avgWiredDensity G bdry q t = (1 / (G.edgeFinset.card : ℝ)) * ∑ e ∈ G.edgeFinset, edgeMargProb (wiredFkProb G bdry (fsc_logistic t) q) e := by
-- proof
  apply StatMech.FK.wpd_avgWiredDensity_eq_sum_edgeMarg G bdry q t

/--
[wpd_wiredFkWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredFkWeight_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredFkWeight G bdry p q ω ≤ fkWeight G p q ω ∧ fkWeight G p q ω ≤ q ^ (Finset.univ.filter bdry).card * wiredFkWeight G bdry p q ω := by
-- proof
  apply StatMech.FK.wpd_wiredFkWeight_le G bdry hp hp1 hq ω

/--
[wpd_wiredFkZ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredFkZ_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {p q : ℝ}
-- given
  (bdry : V → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredFkZ G bdry p q ≤ fkZ G p q ∧ fkZ G p q ≤ q ^ (Finset.univ.filter bdry).card * wiredFkZ G bdry p q := by
-- proof
  apply StatMech.FK.wpd_wiredFkZ_le G bdry hp hp1 hq

/--
[wpd_tiltFreeEnergy_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_tiltFreeEnergy_sub_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℝ}
  {t : ℝ}
-- given
  (bdry : V → Prop)
  (hq : 1 ≤ q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  |ivp2_tiltFreeEnergy G q t - wpd_wiredTiltFreeEnergy G bdry q t| ≤ ((Finset.univ.filter bdry).card : ℝ) / (G.edgeFinset.card : ℝ) * Real.log q := by
-- proof
  apply StatMech.FK.wpd_tiltFreeEnergy_sub_le G bdry hq hE t

/--
[wpd_wiredTiltFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredTiltFreeEnergy_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {q : ℝ}
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (bdry : V → Prop)
  (hq : 1 ≤ q)
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hfree : Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) q t) atTop (𝓝 (g t)))
  (hsv : Tendsto (fun n => ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) q t) atTop (𝓝 (g t)) := by
-- proof
  apply StatMech.FK.wpd_wiredTiltFreeEnergy_tendsto G bdry q hq hE g t hfree hsv

/--
[wpd_wiredAvgDensity_le_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredAvgDensity_le_rightDeriv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {q : ℝ}
  {g : ℝ → ℝ}
  {t ℓ : ℝ}
-- given
  (bdry : V → Prop)
  (hq : 0 < q)
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) q t) atTop (𝓝 (g t)))
  (hℓ : Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t) atTop (𝓝 ℓ)) :
-- imply
  ℓ ≤ pressureRightDeriv g t := by
-- proof
  apply StatMech.FK.wpd_wiredAvgDensity_le_rightDeriv G bdry q hq hE g hg hlim t ℓ hℓ

/--
[wpd_wiredDensityUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_wiredDensityUpperBound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ}
-- given
  (bdry : V → Prop)
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 (g t)))
  (hcol : wpd_AvgWiredDensityCollapse (d := d) N) :
-- imply
  fdd_WiredDensityUpperBound (d := d) N g := by
-- proof
  apply StatMech.FK.wpd_wiredDensityUpperBound G bdry N hE g hg hlim hcol

/--
[wpd_fk_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_fk_uniqueness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
-- given
  (bdry : V → Prop)
  (hEfree : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hwiredlim : ∀ t, Tendsto (fun n => wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 (g t)))
  (hcol : fpd_AvgDensityCollapse d N Gn)
  (hwcol : wpd_AvgWiredDensityCollapse (d := d) N)
  (hflc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt (fun s => freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Iio t) t)
  (hwrc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.wpd_fk_uniqueness G bdry N eb Gn hEfree hEbox hg hfree hwiredlim hcol hwcol hflc hwrc

/--
[wpd_fk_uniqueness_of_surfaceVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean)
-/
@[path]
private lemma wpd_fk_uniqueness_of_surfaceVolume_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
-- given
  (bdry : V → Prop)
  (hEfree : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hsv : Tendsto (fun n => ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 0))
  (hcol : fpd_AvgDensityCollapse d N Gn)
  (hwcol : wpd_AvgWiredDensityCollapse (d := d) N)
  (hflc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt (fun s => freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Iio t) t)
  (hwrc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.wpd_fk_uniqueness_of_surfaceVolume G bdry N eb Gn hEfree hEbox hg hfree hboxfree hsv hcol hwcol hflc hwrc


-- created on 2026-10-23
