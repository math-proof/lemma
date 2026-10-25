import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[fpd_exists_convex_ivPressure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean)
-/
@[path]
private lemma fpd_exists_convex_ivPressure_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {Gn : ℕ → SimpleGraph W}
  [∀ i, DecidableRel (Gn i).Adj]
  {c : ℝ → ℝ}
-- given
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hjux : ∀ m n, Gn (m + n) ≃g Gn m ⊕g Gn n)
  (hbdd : ∀ t, BddBelow (Set.range fun n => (-Real.log (fkZ (Gn n) (fsc_logistic t) 2)) / n))
  (hc : ∀ t, c t ≠ 0)
  (he : ∀ t, Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 (c t))) :
-- imply
  ∃ g : ℝ → ℝ, (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t))) ∧ ConvexOn ℝ univ g := by
-- proof
  apply StatMech.FK.fpd_exists_convex_ivPressure Gn hE hjux hbdd c hc he

/--
[fpd_ivPressure_convexDeriv_facts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean)
-/
@[path]
private lemma fpd_ivPressure_convexDeriv_facts_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {Gn : ℕ → SimpleGraph W}
  [∀ i, DecidableRel (Gn i).Adj]
  {g : ℝ → ℝ}
-- given
  (hconv : ∀ n, ConvexOn ℝ univ (ivp2_tiltFreeEnergy (Gn n) 2))
  (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t))) :
-- imply
  ConvexOn ℝ univ g ∧ (∀ t, HasDerivWithinAt g (pressureRightDeriv g t) (Ioi t) t) ∧ (∀ t, HasDerivWithinAt g (pressureLeftDeriv g t) (Iio t) t) ∧ (∀ t, Tendsto (slope g t) (𝓝[>] t) (𝓝 (pressureRightDeriv g t))) ∧ (∀ t, Tendsto (slope g t) (𝓝[<] t) (𝓝 (pressureLeftDeriv g t))) ∧ (∀ a b, Tendsto (fun n => slope (ivp2_tiltFreeEnergy (Gn n) 2) a b) atTop (𝓝 (slope g a b))) ∧ (∀ t, pressureLeftDeriv g t ≤ pressureRightDeriv g t) ∧ Monotone (pressureRightDeriv g) ∧ Monotone (pressureLeftDeriv g) ∧ {t : ℝ | pressureLeftDeriv g t ≠ pressureRightDeriv g t}.Countable := by
-- proof
  apply StatMech.FK.fpd_ivPressure_convexDeriv_facts Gn hconv g hlim

/--
[fpd_tiltFreeEnergy_deriv_eq_avgDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean)
-/
@[path]
private lemma fpd_tiltFreeEnergy_deriv_eq_avgDensity_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : ℝ}
-- given
  (hE : 0 < G.edgeFinset.card) :
-- imply
  HasDerivAt (ivp2_tiltFreeEnergy G 2) ((1 / (G.edgeFinset.card : ℝ)) * fkExpect G (fsc_logistic t) 2 (fun ω => (openCount G ω : ℝ))) t := by
-- proof
  apply StatMech.FK.fpd_tiltFreeEnergy_deriv_eq_avgDensity G hE t

/--
[fpd_deriv_interchange_of_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean)
-/
@[path]
private lemma fpd_deriv_interchange_of_differentiable_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {l : Filter κ}
  [l.NeBot]
  {gn : κ → ℝ → ℝ}
  {g : ℝ → ℝ}
  {dn : κ → ℝ → ℝ}
  {t : ℝ}
-- given
  (hconv : ∀ i, ConvexOn ℝ univ (gn i))
  (hderiv : ∀ i t, HasDerivAt (gn i) (dn i t) t)
  (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (g x)))
  (hg : ConvexOn ℝ univ g)
  (hdiff : pressureLeftDeriv g t = pressureRightDeriv g t) :
-- imply
  Tendsto (fun i => dn i t) l (𝓝 (pressureRightDeriv g t)) := by
-- proof
  apply StatMech.FK.fpd_deriv_interchange_of_differentiable G gn g dn hconv hderiv hlim t hg hdiff

/--
[fpd_ivPressureDeriv_eq_avgDensity_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean)
-/
@[path]
private lemma fpd_ivPressureDeriv_eq_avgDensity_limit_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {Gn : ℕ → SimpleGraph W}
  [∀ i, DecidableRel (Gn i).Adj]
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hdiff : pressureLeftDeriv g t = pressureRightDeriv g t) :
-- imply
  Tendsto (fun n => fpd_avgDensity (Gn n) t) atTop (𝓝 (pressureRightDeriv g t)) := by
-- proof
  apply StatMech.FK.fpd_ivPressureDeriv_eq_avgDensity_limit G Gn hE g hg hlim t hdiff

/--
[fpd_freeDensity_at_diff_of_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean)
-/
@[path]
private lemma fpd_freeDensity_at_diff_of_collapse_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d N : ℕ}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hcol : fpd_AvgDensityCollapse d N Gn)
  (hdiff : pressureLeftDeriv g t = pressureRightDeriv g t) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t := by
-- proof
  apply StatMech.FK.fpd_freeDensity_at_diff_of_collapse G d N Gn hE g hg hlim hcol e' t hdiff

/--
[fpd_homogeneousFreeEnergyData_of_densityDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean)
-/
@[path]
private lemma fpd_homogeneousFreeEnergyData_of_densityDeriv_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d N : ℕ}
  {g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hres : fpd_IVDensityIsOneSidedDeriv d N g) :
-- imply
  fuc_HomogeneousFreeEnergyData d N := by
-- proof
  apply StatMech.FK.fpd_homogeneousFreeEnergyData_of_densityDeriv G d N hg hres

/--
[fpd_fk_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean)
-/
@[path]
private lemma fpd_fk_uniqueness_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hres : fpd_IVDensityIsOneSidedDeriv d N g) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.fpd_fk_uniqueness G d N eb hg hres

/--
[fpd_densityDeriv_imp_fsc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean)
-/
@[path]
private lemma fpd_densityDeriv_imp_fsc_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d N : ℕ}
  {g : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
-- given
  (hg : ConvexOn ℝ univ g)
  (hres : fpd_IVDensityIsOneSidedDeriv d N g) :
-- imply
  fsc_FreeEnergyData d N e' := by
-- proof
  apply StatMech.FK.fpd_densityDeriv_imp_fsc G d N hg hres e'

/--
[fpd_homogeneousFreeEnergyData_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean)
-/
@[path]
private lemma fpd_homogeneousFreeEnergyData_iff_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d N : ℕ} :
-- imply
  fuc_HomogeneousFreeEnergyData d N ↔ ∃ g : ℝ → ℝ, ConvexOn ℝ univ g ∧ fpd_IVDensityIsOneSidedDeriv d N g := by
-- proof
  apply StatMech.FK.fpd_homogeneousFreeEnergyData_iff G d N


-- created on 2026-10-23
