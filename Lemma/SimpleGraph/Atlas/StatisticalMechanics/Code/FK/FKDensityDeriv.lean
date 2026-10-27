import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv.Part2
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[fdd_avgLimit_le_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_avgLimit_le_rightDeriv_eq
  {l : Filter κ}
  [l.NeBot]
  {gn : κ → ℝ → ℝ}
  {g : ℝ → ℝ}
  {dn : κ → ℝ → ℝ}
  {t ℓ : ℝ}
-- given
  (hconv : ∀ i, ConvexOn ℝ univ (gn i))
  (hderiv : ∀ i t, HasDerivAt (gn i) (dn i t) t)
  (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (g x)))
  (hg : ConvexOn ℝ univ g)
  (hℓ : Tendsto (fun i => dn i t) l (𝓝 ℓ)) :
-- imply
  ℓ ≤ pressureRightDeriv g t := by
-- proof
  apply StatMech.FK.fdd_avgLimit_le_rightDeriv gn g dn hconv hderiv hlim t ℓ hg hℓ

/--
[fdd_leftDeriv_le_avgLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_leftDeriv_le_avgLimit_eq
  {l : Filter κ}
  [l.NeBot]
  {gn : κ → ℝ → ℝ}
  {g : ℝ → ℝ}
  {dn : κ → ℝ → ℝ}
  {t ℓ : ℝ}
-- given
  (hconv : ∀ i, ConvexOn ℝ univ (gn i))
  (hderiv : ∀ i t, HasDerivAt (gn i) (dn i t) t)
  (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (g x)))
  (hg : ConvexOn ℝ univ g)
  (hℓ : Tendsto (fun i => dn i t) l (𝓝 ℓ)) :
-- imply
  pressureLeftDeriv g t ≤ ℓ := by
-- proof
  apply StatMech.FK.fdd_leftDeriv_le_avgLimit gn g dn hconv hderiv hlim t ℓ hg hℓ

/--
[fdd_avgDensity_le_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_avgDensity_le_rightDeriv_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {Gn : ℕ → SimpleGraph W}
  [∀ i, DecidableRel (Gn i).Adj]
  {g : ℝ → ℝ}
  {t ℓ : ℝ}
-- given
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hℓ : Tendsto (fun n => fpd_avgDensity (Gn n) t) atTop (𝓝 ℓ)) :
-- imply
  ℓ ≤ pressureRightDeriv g t := by
-- proof
  apply StatMech.FK.fdd_avgDensity_le_rightDeriv Gn hE g hg hlim t ℓ hℓ

/--
[fdd_leftDeriv_le_avgDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_leftDeriv_le_avgDensity_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {Gn : ℕ → SimpleGraph W}
  [∀ i, DecidableRel (Gn i).Adj]
  {g : ℝ → ℝ}
  {t ℓ : ℝ}
-- given
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hℓ : Tendsto (fun n => fpd_avgDensity (Gn n) t) atTop (𝓝 ℓ)) :
-- imply
  pressureLeftDeriv g t ≤ ℓ := by
-- proof
  apply StatMech.FK.fdd_leftDeriv_le_avgDensity Gn hE g hg hlim t ℓ hℓ

/--
[fdd_freeDensity_le_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_freeDensity_le_rightDeriv_eq
  {d : ℕ}
  {N : ℕ}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hcol : fpd_AvgDensityCollapse d N Gn) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ≤ pressureRightDeriv g t := by
-- proof
  apply StatMech.FK.fdd_freeDensity_le_rightDeriv N Gn hE g hg hlim hcol e' t

/--
[fdd_leftDeriv_le_freeDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_leftDeriv_le_freeDensity_eq
  {d : ℕ}
  {N : ℕ}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hcol : fpd_AvgDensityCollapse d N Gn) :
-- imply
  pressureLeftDeriv g t ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) := by
-- proof
  apply StatMech.FK.fdd_leftDeriv_le_freeDensity N Gn hE g hg hlim hcol e' t

/--
[fdd_freeDensity_bracket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_freeDensity_bracket_eq
  {d : ℕ}
  {N : ℕ}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hcol : fpd_AvgDensityCollapse d N Gn) :
-- imply
  pressureLeftDeriv g t ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ∧ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ≤ pressureRightDeriv g t := by
-- proof
  apply StatMech.FK.fdd_freeDensity_bracket N Gn hE g hg hlim hcol e' t

/--
[fdd_free_is_leftDeriv_at_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_free_is_leftDeriv_at_diff_eq
  {d : ℕ}
  {N : ℕ}
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
  apply StatMech.FK.fdd_free_is_leftDeriv_at_diff N Gn hE g hg hlim hcol e' t hdiff

/--
[fdd_eq_leftDeriv_of_bracket_leftContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_eq_leftDeriv_of_bracket_leftContinuous_eq
  {d : ℕ}
  {g a : ℝ → ℝ}
  {t : ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hbL : ∀ s, pressureLeftDeriv g s ≤ a s)
  (hbR : ∀ s, a s ≤ pressureRightDeriv g s)
  (hlc : ContinuousWithinAt a (Iio t) t) :
-- imply
  a t = pressureLeftDeriv g t := by
-- proof
  apply StatMech.FK.fdd_eq_leftDeriv_of_bracket_leftContinuous hg hbL hbR hlc

/--
[fdd_eq_rightDeriv_of_bracket_rightContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_eq_rightDeriv_of_bracket_rightContinuous_eq
  {d : ℕ}
  {g a : ℝ → ℝ}
  {t : ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hbL : ∀ s, pressureLeftDeriv g s ≤ a s)
  (hbR : ∀ s, a s ≤ pressureRightDeriv g s)
  (hrc : ContinuousWithinAt a (Ioi t) t) :
-- imply
  a t = pressureRightDeriv g t := by
-- proof
  apply StatMech.FK.fdd_eq_rightDeriv_of_bracket_rightContinuous hg hbL hbR hrc

/--
[fdd_free_is_leftDeriv_of_leftContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_free_is_leftDeriv_of_leftContinuous_eq
  {d : ℕ}
  {N : ℕ}
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
  (hlc : ContinuousWithinAt (fun s => freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Iio t) t) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t := by
-- proof
  apply StatMech.FK.fdd_free_is_leftDeriv_of_leftContinuous N Gn hE g hg hlim hcol e' t hlc

/--
[fdd_leftDeriv_le_wiredDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_leftDeriv_le_wiredDensity_eq
  {d : ℕ}
  {N : ℕ}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hcol : fpd_AvgDensityCollapse d N Gn) :
-- imply
  pressureLeftDeriv g t ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) := by
-- proof
  apply StatMech.FK.fdd_leftDeriv_le_wiredDensity N Gn hE g hg hlim hcol e' t

/--
[fdd_wired_is_rightDeriv_of_upperBound_rightContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_wired_is_rightDeriv_of_upperBound_rightContinuous_eq
  {d : ℕ}
  {N : ℕ}
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
  (hub : fdd_WiredDensityUpperBound (d := d) N g)
  (hrc : ContinuousWithinAt (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureRightDeriv g t := by
-- proof
  apply StatMech.FK.fdd_wired_is_rightDeriv_of_upperBound_rightContinuous N Gn hE hg hlim hcol hub e' t hrc

/--
[fdd_IVDensityIsOneSidedDeriv_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_IVDensityIsOneSidedDeriv_iff_eq
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ} :
-- imply
  fpd_IVDensityIsOneSidedDeriv d N g ↔ fdd_WiredDensityIsRightDeriv (d := d) N g ∧ fdd_FreeDensityIsLeftDeriv (d := d) N g := by
-- proof
  apply StatMech.FK.fdd_IVDensityIsOneSidedDeriv_iff N g

/--
[fdd_IVDensityIsOneSidedDeriv_of_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_IVDensityIsOneSidedDeriv_of_halves_eq
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ}
-- given
  (hwired : fdd_WiredDensityIsRightDeriv (d := d) N g)
  (hfree : fdd_FreeDensityIsLeftDeriv (d := d) N g) :
-- imply
  fpd_IVDensityIsOneSidedDeriv d N g := by
-- proof
  apply StatMech.FK.fdd_IVDensityIsOneSidedDeriv_of_halves N g hwired hfree

/--
[fdd_fk_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_fk_uniqueness_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hwired : fdd_WiredDensityIsRightDeriv (d := d) N g)
  (hfree : fdd_FreeDensityIsLeftDeriv (d := d) N g) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.fdd_fk_uniqueness N eb hg hwired hfree

/--
[fdd_fk_uniqueness_of_primitives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_fk_uniqueness_of_primitives_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {Gn : ℕ → SimpleGraph (boxVerts d N)}
  [∀ n, DecidableRel (Gn n).Adj]
  {g : ℝ → ℝ}
-- given
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
  (hcol : fpd_AvgDensityCollapse d N Gn)
  (hflc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt (fun s => freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Iio t) t)
  (hwub : fdd_WiredDensityUpperBound (d := d) N g)
  (hwrc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.fdd_fk_uniqueness_of_primitives N eb Gn hE hg hlim hcol hflc hwub hwrc

/--
[fdd_halves_imp_fsc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDensityDeriv.lean)
-/
@[path]
private lemma fdd_halves_imp_fsc_eq
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
-- given
  (hg : ConvexOn ℝ univ g)
  (hwired : fdd_WiredDensityIsRightDeriv (d := d) N g)
  (hfree : fdd_FreeDensityIsLeftDeriv (d := d) N g) :
-- imply
  fsc_FreeEnergyData d N e' := by
-- proof
  apply StatMech.FK.fdd_halves_imp_fsc N hg hwired hfree e'


-- created on 2026-10-23
