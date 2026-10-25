import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.IVPressureConvex.Part5
open MeasureTheory Set Filter Topology Real Finset StatMech StatMech.FK


/--
[ivp2_expmul_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_expmul_hasDerivAt_eq
  {c t : ℝ} :
-- imply
  HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * t)) t := by
-- proof
  apply StatMech.FK.ivp2_expmul_hasDerivAt c t

/--
[ivp2_sumExp_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_sumExp_hasDerivAt_eq
  [Fintype ι]
  {b a : ι → ℝ}
  {t : ℝ} :
-- imply
  HasDerivAt (fun s => ∑ i, b i * Real.exp (a i * s)) (∑ i, b i * a i * Real.exp (a i * t)) t := by
-- proof
  apply StatMech.FK.ivp2_sumExp_hasDerivAt b a t

/--
[ivp2_Ssum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_Ssum_pos_eq
  [Fintype ι]
  {w a : ι → ℝ}
  {t : ℝ}
-- given
  (hw : ∀ i, 0 ≤ w i)
  (hpos : ∃ i, 0 < w i) :
-- imply
  0 < ivp2_Ssum w a t := by
-- proof
  apply StatMech.FK.ivp2_Ssum_pos w a hw hpos t

/--
[ivp2_Ssum_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_Ssum_hasDerivAt_eq
  [Fintype ι]
  {w a : ι → ℝ}
  {t : ℝ} :
-- imply
  HasDerivAt (ivp2_Ssum w a) (ivp2_S1 w a t) t := by
-- proof
  apply StatMech.FK.ivp2_Ssum_hasDerivAt w a t

/--
[ivp2_S1_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_S1_hasDerivAt_eq
  [Fintype ι]
  {w a : ι → ℝ}
  {t : ℝ} :
-- imply
  HasDerivAt (ivp2_S1 w a) (ivp2_S2 w a t) t := by
-- proof
  apply StatMech.FK.ivp2_S1_hasDerivAt w a t

/--
[ivp2_cauchy_schwarz_cgf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_cauchy_schwarz_cgf_eq
  [Fintype ι]
  {w a : ι → ℝ}
  {t : ℝ}
-- given
  (hw : ∀ i, 0 ≤ w i) :
-- imply
  (ivp2_S1 w a t) ^ 2 ≤ (ivp2_S2 w a t) * (ivp2_Ssum w a t) := by
-- proof
  apply StatMech.FK.ivp2_cauchy_schwarz_cgf w a hw t

/--
[ivp2_Kcgf_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_Kcgf_hasDerivAt_eq
  [Fintype ι]
  {w a : ι → ℝ}
  {t : ℝ}
-- given
  (hw : ∀ i, 0 ≤ w i)
  (hpos : ∃ i, 0 < w i) :
-- imply
  HasDerivAt (ivp2_Kcgf w a) (ivp2_S1 w a t / ivp2_Ssum w a t) t := by
-- proof
  apply StatMech.FK.ivp2_Kcgf_hasDerivAt w a hw hpos t

/--
[ivp2_deriv_Kcgf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_deriv_Kcgf_eq
  [Fintype ι]
  {w a : ι → ℝ}
-- given
  (hw : ∀ i, 0 ≤ w i)
  (hpos : ∃ i, 0 < w i) :
-- imply
  deriv (ivp2_Kcgf w a) = fun t => ivp2_S1 w a t / ivp2_Ssum w a t := by
-- proof
  apply StatMech.FK.ivp2_deriv_Kcgf w a hw hpos

/--
[ivp2_Kcgf_deriv2_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_Kcgf_deriv2_hasDerivAt_eq
  [Fintype ι]
  {w a : ι → ℝ}
  {t : ℝ}
-- given
  (hw : ∀ i, 0 ≤ w i)
  (hpos : ∃ i, 0 < w i) :
-- imply
  HasDerivAt (fun s => ivp2_S1 w a s / ivp2_Ssum w a s) ((ivp2_S2 w a t * ivp2_Ssum w a t - ivp2_S1 w a t * ivp2_S1 w a t) / (ivp2_Ssum w a t) ^ 2) t := by
-- proof
  apply StatMech.FK.ivp2_Kcgf_deriv2_hasDerivAt w a hw hpos t

/--
[ivp2_Kcgf_deriv2_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_Kcgf_deriv2_nonneg_eq
  [Fintype ι]
  {w a : ι → ℝ}
  {t : ℝ}
-- given
  (hw : ∀ i, 0 ≤ w i)
  (hpos : ∃ i, 0 < w i) :
-- imply
  0 ≤ (deriv^[2] (ivp2_Kcgf w a)) t := by
-- proof
  apply StatMech.FK.ivp2_Kcgf_deriv2_nonneg w a hw hpos t

/--
[ivp2_Kcgf_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_Kcgf_convexOn_eq
  [Fintype ι]
  {w a : ι → ℝ}
-- given
  (hw : ∀ i, 0 ≤ w i)
  (hpos : ∃ i, 0 < w i) :
-- imply
  ConvexOn ℝ univ (ivp2_Kcgf w a) := by
-- proof
  apply StatMech.FK.ivp2_Kcgf_convexOn w a hw hpos

/--
[ivp2_edgeProduct_logistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_edgeProduct_logistic_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  edgeProduct G (fsc_logistic t) ω = Real.exp (openCount G ω * t) / (1 + Real.exp t) ^ G.edgeFinset.card := by
-- proof
  apply StatMech.FK.ivp2_edgeProduct_logistic G t ω

/--
[ivp2_fkWeight_logistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_fkWeight_logistic_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t q : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  fkWeight G (fsc_logistic t) q ω = (q ^ numClusters G ω * Real.exp ((openCount G ω : ℝ) * t)) / (1 + Real.exp t) ^ G.edgeFinset.card := by
-- proof
  apply StatMech.FK.ivp2_fkWeight_logistic G t q ω

/--
[ivp2_fkZ_logistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_fkZ_logistic_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t q : ℝ} :
-- imply
  fkZ G (fsc_logistic t) q = ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t / (1 + Real.exp t) ^ G.edgeFinset.card := by
-- proof
  apply StatMech.FK.ivp2_fkZ_logistic G t q

/--
[ivp2_tiltFreeEnergy_eq_Kcgf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_tiltFreeEnergy_eq_Kcgf_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
  {t : ℝ}
-- given
  (hq : 0 < q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  ivp2_tiltFreeEnergy G q t = (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t := by
-- proof
  apply StatMech.FK.ivp2_tiltFreeEnergy_eq_Kcgf G q hq hE t

/--
[ivp2_tiltFreeEnergy_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_tiltFreeEnergy_convexOn_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
-- given
  (hq : 0 < q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  ConvexOn ℝ univ (ivp2_tiltFreeEnergy G q) := by
-- proof
  apply StatMech.FK.ivp2_tiltFreeEnergy_convexOn G q hq hE

/--
[ivp2_convexOn_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_convexOn_of_tendsto_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {l : Filter κ}
  [l.NeBot]
  {f : κ → ℝ → ℝ}
  {g : ℝ → ℝ}
-- given
  (hconv : ∀ i, ConvexOn ℝ univ (f i))
  (hlim : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x))) :
-- imply
  ConvexOn ℝ univ g := by
-- proof
  apply StatMech.FK.ivp2_convexOn_of_tendsto G f g hconv hlim

/--
[ivp2_limitFreeEnergy_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_limitFreeEnergy_convexOn_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {l : Filter κ}
  [l.NeBot]
  [Fintype W]
  [DecidableEq W]
  {Gn : κ → SimpleGraph W}
  [∀ i, DecidableRel (Gn i).Adj]
  {q : ℝ}
  {g : ℝ → ℝ}
-- given
  (hq : 0 < q)
  (hE : ∀ i, 0 < (Gn i).edgeFinset.card)
  (hlim : ∀ t, Tendsto (fun i => ivp2_tiltFreeEnergy (Gn i) q t) l (𝓝 (g t))) :
-- imply
  ConvexOn ℝ univ g := by
-- proof
  apply StatMech.FK.ivp2_limitFreeEnergy_convexOn G Gn q hq hE g hlim

/--
[ivp2_tiltFreeEnergy_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_tiltFreeEnergy_hasDerivAt_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
  {t : ℝ}
-- given
  (hq : 0 < q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  HasDerivAt (ivp2_tiltFreeEnergy G q) ((1 / (G.edgeFinset.card : ℝ)) * (ivp2_S1 (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t / ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t)) t := by
-- proof
  apply StatMech.FK.ivp2_tiltFreeEnergy_hasDerivAt G q hq hE t

/--
[ivp2_cgfMean_eq_openCount_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_cgfMean_eq_openCount_expect_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
  {t : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  fkExpect G (fsc_logistic t) q (fun ω => (openCount G ω : ℝ)) = ivp2_S1 (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t / ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t := by
-- proof
  apply StatMech.FK.ivp2_cgfMean_eq_openCount_expect G q hq t

/--
[ivp2_freeEnergyData_convex_part](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_freeEnergyData_convex_part_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {l : Filter κ}
  [l.NeBot]
  [Fintype W]
  [DecidableEq W]
  {Gn : κ → SimpleGraph W}
  [∀ i, DecidableRel (Gn i).Adj]
  {q : ℝ}
  {g : ℝ → ℝ}
-- given
  (hq : 0 < q)
  (hE : ∀ i, 0 < (Gn i).edgeFinset.card)
  (hlim : ∀ t, Tendsto (fun i => ivp2_tiltFreeEnergy (Gn i) q t) l (𝓝 (g t))) :
-- imply
  ConvexOn ℝ univ g := by
-- proof
  apply StatMech.FK.ivp2_freeEnergyData_convex_part G Gn q hq hE g hlim

/--
[ivp2_softplus_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean)
-/
@[path]
private lemma ivp2_softplus_convexOn_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ConvexOn ℝ univ ivp2_softplus := by
-- proof
  apply StatMech.FK.ivp2_softplus_convexOn G


-- created on 2026-10-23
