import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.AdditiveGluing
open SimpleGraph Filter Topology Set MeasureTheory StatMech StatMech.FK


/--
[agl_sumEquiv_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_sumEquiv_inl_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {a : {x // P x}} :
-- imply
  agl_sumEquiv P (Sum.inl a) = (a : U) := by
-- proof
  apply StatMech.FK.agl_sumEquiv_inl K₀ a

/--
[agl_sumEquiv_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_sumEquiv_inr_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {b : {x // ¬ P x}} :
-- imply
  agl_sumEquiv P (Sum.inr b) = (b : U) := by
-- proof
  apply StatMech.FK.agl_sumEquiv_inr K₀ b

/--
[agl_glueGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_glueGraph_adj_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {u v : {x // P x} ⊕ {x // ¬ P x}} :
-- imply
  (agl_glueGraph K₀ P).Adj u v ↔ K₀.Adj (agl_sumEquiv P u) (agl_sumEquiv P v) := by
-- proof
  apply StatMech.FK.agl_glueGraph_adj K₀ u v

/--
[agl_partitionCrossInterface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_partitionCrossInterface_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj] :
-- imply
  fis_CrossInterface (agl_left K₀ P) (agl_right K₀ P) (agl_glueGraph K₀ P) := by
-- proof
  apply StatMech.FK.agl_partitionCrossInterface K₀

/--
[agl_fkZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_fkZ_eq_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {p q : ℝ} :
-- imply
  fkZ K₀ p q = fkZ (agl_glueGraph K₀ P) p q := by
-- proof
  apply StatMech.FK.agl_fkZ_eq K₀ p q

/--
[agl_neglog_partition_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_neglog_partition_le_eq
  [Fintype U]
  [DecidableEq U]
  {K₀ : SimpleGraph U}
  [DecidableRel K₀.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  -Real.log (fkZ K₀ p q) ≤ -Real.log (fkZ (agl_left K₀ P) p q) + -Real.log (fkZ (agl_right K₀ P) p q) - (agl_interfaceCard K₀ P : ℝ) * Real.log (1 - p) := by
-- proof
  apply StatMech.FK.agl_neglog_partition_le K₀ hp hp1 hq

/--
[agl_nn_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_nn_translate_eq
  {d : ℕ}
  {v x y : Site d} :
-- imply
  (hypercubicLattice d).Adj (x + v) (y + v) ↔ (hypercubicLattice d).Adj x y := by
-- proof
  apply StatMech.FK.agl_nn_translate d v x y

/--
[agl_fkZ_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_fkZ_translate_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {d : ℕ}
  {v : Site d}
  {f : V → Site d}
  {g : W → Site d}
  {φ : V ≃ W}
  {p q : ℝ}
  [DecidableRel ((hypercubicLattice d).comap f).Adj]
  [DecidableRel ((hypercubicLattice d).comap g).Adj]
-- given
  (hfg : ∀ x, g (φ x) = f x + v) :
-- imply
  fkZ ((hypercubicLattice d).comap f) p q = fkZ ((hypercubicLattice d).comap g) p q := by
-- proof
  apply StatMech.FK.agl_fkZ_translate d v f g φ hfg p q

/--
[agl_left_block_fkZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_left_block_fkZ_eq_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {N m : ℕ}
  [DecidablePred P]
  {v : Site d}
  {φ : boxVerts d m ≃ {x // P x}}
  {p q : ℝ}
-- given
  (P : boxVerts d N → Prop)
  (hφ : ∀ y : boxVerts d m, ((φ y : boxVerts d N) : Site d) = (y : Site d) + v) :
-- imply
  fkZ (agl_left (boxGraph d N) P) p q = fkZ (boxGraph d m) p q := by
-- proof
  apply StatMech.FK.agl_left_block_fkZ_eq N m P v φ hφ p q

/--
[agl_right_block_fkZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_right_block_fkZ_eq_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {N m : ℕ}
  [DecidablePred P]
  {v : Site d}
  {φ : boxVerts d m ≃ {x // ¬ P x}}
  {p q : ℝ}
-- given
  (P : boxVerts d N → Prop)
  (hφ : ∀ y : boxVerts d m, ((φ y : boxVerts d N) : Site d) = (y : Site d) + v) :
-- imply
  fkZ (agl_right (boxGraph d N) P) p q = fkZ (boxGraph d m) p q := by
-- proof
  apply StatMech.FK.agl_right_block_fkZ_eq N m P v φ hφ p q

/--
[agl_subseq_almost_mono_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_subseq_almost_mono_converges_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {g : ℕ → ℝ}
  {K : ℕ → ℕ}
  {δ : ℕ → ℝ}
-- given
  (hδ : ∀ j, 0 ≤ δ j)
  (hsum : Summable δ)
  (hmono : ∀ j, g (K j) - δ j ≤ g (K (j + 1)))
  (hbdd : BddAbove (Set.range fun j => g (K j))) :
-- imply
  ∃ L, Tendsto (fun j => g (K j)) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.agl_subseq_almost_mono_converges g K δ hδ hsum hmono hbdd

/--
[agl_full_from_subseq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_full_from_subseq_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {g : ℕ → ℝ}
  {K : ℕ → ℕ}
  {L : ℝ}
  {bj : ℕ → ℕ}
  {osc : ℕ → ℝ}
-- given
  (hsub : Tendsto (fun j => g (K j)) atTop (𝓝 L))
  (hbj : Tendsto bj atTop atTop)
  (hosc : Tendsto osc atTop (𝓝 0))
  (hsand : ∀ n, |g n - g (K (bj n))| ≤ osc (bj n)) :
-- imply
  Tendsto g atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.agl_full_from_subseq g K L hsub bj hbj osc hosc hsand

/--
[agl_perVolume_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_perVolume_converges_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {g : ℕ → ℝ}
  {K : ℕ → ℕ}
  {δ osc : ℕ → ℝ}
  {bj : ℕ → ℕ}
-- given
  (hδ : ∀ j, 0 ≤ δ j)
  (hsum : Summable δ)
  (hmono : ∀ j, g (K j) - δ j ≤ g (K (j + 1)))
  (hbdd : BddAbove (Set.range fun j => g (K j)))
  (hbj : Tendsto bj atTop atTop)
  (hosc : Tendsto osc atTop (𝓝 0))
  (hsand : ∀ n, |g n - g (K (bj n))| ≤ osc (bj n)) :
-- imply
  ∃ L, Tendsto g atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.agl_perVolume_converges g K δ osc bj hδ hsum hmono hbdd hbj hosc hsand

/--
[agl_K_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_K_zero_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W] :
-- imply
  agl_K 0 = 1 := by
-- proof
  apply StatMech.FK.agl_K_zero

/--
[agl_K_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_K_succ_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {j : ℕ} :
-- imply
  agl_K (j + 1) = 2 * agl_K j + 1 := by
-- proof
  apply StatMech.FK.agl_K_succ j

/--
[agl_K_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_K_pos_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {j : ℕ} :
-- imply
  1 ≤ agl_K j := by
-- proof
  apply StatMech.FK.agl_K_pos j

/--
[agl_K_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_K_tendsto_atTop_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W] :
-- imply
  Tendsto agl_K atTop atTop := by
-- proof
  apply StatMech.FK.agl_K_tendsto_atTop

/--
[agl_g_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_g_eq_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {d : ℕ}
  {t : ℝ}
  {n : ℕ} :
-- imply
  ivp2_tiltFreeEnergy (boxGraph d n) 2 t = -(agl_u d t n / agl_E d n) + Real.log (1 + Real.exp t) := by
-- proof
  apply StatMech.FK.agl_g_eq d t n

/--
[agl_boxTiltFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_boxTiltFreeEnergy_tendsto_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {d : ℕ}
  {t : ℝ}
  {bj : ℕ → ℕ}
  {osc : ℕ → ℝ}
-- given
  (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card)
  (hdoubling : agl_AdditiveDoublingBound d t)
  (hbdd : ∃ M : ℝ, ∀ j, |agl_u d t (agl_K j) / agl_E d (agl_K j)| ≤ M)
  (hbj : Tendsto bj atTop atTop)
  (hosc : Tendsto osc atTop (𝓝 0))
  (hsand : ∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 t - ivp2_tiltFreeEnergy (boxGraph d (agl_K (bj n))) 2 t| ≤ osc (bj n)) :
-- imply
  ∃ L : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.agl_boxTiltFreeEnergy_tendsto d t hbox hdoubling hbdd bj hbj osc hosc hsand

/--
[agl_doublingStep_of_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_doublingStep_of_partition_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {d : ℕ}
  {t : ℝ}
  {K : ℕ}
  [DecidablePred P]
  {v : Site d}
  {φ : boxVerts d K ≃ {x // P x}}
  {IR : ℝ}
-- given
  (P : boxVerts d (2 * K + 1) → Prop)
  (hφ : ∀ y : boxVerts d K, ((φ y : boxVerts d (2 * K + 1)) : Site d) = (y : Site d) + v)
  (hIR : 0 ≤ IR)
  (hRight : -Real.log (fkZ (agl_right (boxGraph d (2 * K + 1)) P) (fsc_logistic t) 2) ≤ ((2:ℝ) ^ d - 1) * agl_u d t K + IR * (-Real.log (1 - fsc_logistic t))) :
-- imply
  agl_u d t (2 * K + 1) ≤ (2 : ℝ) ^ d * agl_u d t K + ((agl_interfaceCard (boxGraph d (2 * K + 1)) P : ℝ) + IR) * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.agl_doublingStep_of_partition d t K P v φ hφ IR hIR hRight

/--
[agl_rightBlock_recursion_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_rightBlock_recursion_satisfiable_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {d : ℕ}
  {t : ℝ}
  {K : ℕ}
  [DecidablePred P]
-- given
  (P : boxVerts d (2 * K + 1) → Prop) :
-- imply
  ∃ IR : ℝ, 0 ≤ IR ∧ -Real.log (fkZ (agl_right (boxGraph d (2 * K + 1)) P) (fsc_logistic t) 2) ≤ ((2:ℝ) ^ d - 1) * agl_u d t K + IR * (-Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.agl_rightBlock_recursion_satisfiable d t K P

/--
[agl_exists_convex_ivPressure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_exists_convex_ivPressure_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hdata : ∀ t, agl_AdditiveBoxFeketeData d t) :
-- imply
  ∃ g : ℝ → ℝ, (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t))) ∧ ConvexOn ℝ univ g := by
-- proof
  apply StatMech.FK.agl_exists_convex_ivPressure d hd hE hdata

/--
[agl_fk_uniqueness_of_additiveData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_fk_uniqueness_of_additiveData_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hdata : ∀ t, agl_AdditiveBoxFeketeData d t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.agl_fk_uniqueness_of_additiveData d hd N eb heb hEbox hdata

/--
[agl_additiveDoublingBound_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_additiveDoublingBound_satisfiable_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {d : ℕ}
  {d : ℕ}
  {c : ℝ}
-- given
  (hd : 1 ≤ d)
  (hc : 0 ≤ c) :
-- imply
  ∃ (u E : ℕ → ℝ), (∃ (I : ℕ → ℝ), (∀ j, 0 ≤ I j) ∧ Summable (fun j => I j / E (agl_K (j + 1))) ∧ (∀ j, u (agl_K (j + 1)) ≤ (2 : ℝ) ^ d * u (agl_K j) + I j * c) ∧ (∀ j, |(2 : ℝ) ^ d * E (agl_K j) - E (agl_K (j + 1))| ≤ I j)) := by
-- proof
  apply StatMech.FK.agl_additiveDoublingBound_satisfiable d d hd c hc

/--
[agl_residue_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean)
-/
@[path]
private lemma agl_residue_remark_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {d : ℕ} :
-- imply
  True := by
-- proof
  apply StatMech.FK.agl_residue_remark d


-- created on 2026-10-23
