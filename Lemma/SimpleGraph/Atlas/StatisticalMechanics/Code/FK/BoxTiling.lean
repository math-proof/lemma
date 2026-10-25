import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[bxt_g_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean)
-/
@[path]
private lemma bxt_g_eq_eq
  {d : ℕ}
  {d : ℕ}
  {t : ℝ}
  {n : ℕ} :
-- imply
  ivp2_tiltFreeEnergy (boxGraph d n) 2 t = - (bxt_u d t n / bxt_E d n) + Real.log (1 + Real.exp t) := by
-- proof
  apply StatMech.FK.bxt_g_eq d t n

/--
[bxt_E_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean)
-/
@[path]
private lemma bxt_E_nonneg_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  0 ≤ bxt_E d n := by
-- proof
  apply StatMech.FK.bxt_E_nonneg d n

/--
[bxt_perVolume_doubling_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean)
-/
@[path]
private lemma bxt_perVolume_doubling_step_eq
  {d : ℕ}
  {a A e E K c i : ℝ}
-- given
  (he : 0 < e)
  (hE : 0 < E)
  (hc : 0 ≤ c)
  (hi : 0 ≤ i)
  (hA : A ≤ K * a + i * c)
  (hedge : |K * e - E| ≤ i) :
-- imply
  - (a / e) - (|a| / e + c) * (i / E) ≤ - (A / E) := by
-- proof
  apply StatMech.FK.bxt_perVolume_doubling_step he hE hc hi hA hedge

/--
[bxt_perVolumeData_of_doubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean)
-/
@[path]
private lemma bxt_perVolumeData_of_doubling_eq
  {d : ℕ}
  {t : ℝ}
  {osc : ℕ → ℝ}
-- given
  (hbox : ∀ j, 0 < (boxGraph d (2 ^ j)).edgeFinset.card)
  (hdoubling : bxt_NegLogDoublingBound d t)
  (hbdd : ∃ M : ℝ, ∀ j, |bxt_u d t (2 ^ j) / bxt_E d (2 ^ j)| ≤ M)
  (hosc : Tendsto osc atTop (𝓝 0))
  (hsand : ∀ n, 1 ≤ n → |ivp2_tiltFreeEnergy (boxGraph d n) 2 t - ivp2_tiltFreeEnergy (boxGraph d (2 ^ (Nat.log 2 n))) 2 t| ≤ osc (Nat.log 2 n)) :
-- imply
  bpv_PerVolumeFreeEnergyData d t := by
-- proof
  apply StatMech.FK.bxt_perVolumeData_of_doubling t hbox hdoubling hbdd osc hosc hsand

/--
[bxt_doublingBound_of_crossSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean)
-/
@[path]
private lemma bxt_doublingBound_of_crossSplit_eq
  {d : ℕ}
  {t : ℝ}
  {j : ℕ}
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {K : SimpleGraph (boxVerts d (2 ^ j) ⊕ W)}
  [DecidableRel K.Adj]
  {φ : boxGraph d (2 ^ (j + 1)) ≃g K}
-- given
  (hci : fis_CrossInterface (boxGraph d (2 ^ j)) H K)
  (hH : (fkZ (boxGraph d (2 ^ j)) (fsc_logistic t) 2) ^ (2 ^ d - 1) ≤ fkZ H (fsc_logistic t) 2) :
-- imply
  bxt_u d t (2 ^ (j + 1)) ≤ (2 : ℝ) ^ d * bxt_u d t (2 ^ j) + (fis_interface (boxGraph d (2 ^ j)) H K).card * (- Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.bxt_doublingBound_of_crossSplit t j H K hci φ hH

/--
[bxt_negLogDoublingBound_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean)
-/
@[path]
private lemma bxt_negLogDoublingBound_satisfiable_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  ∃ (u E : ℕ → ℝ) (c : ℝ), (∃ (I : ℕ → ℝ), (∀ j, 0 ≤ I j) ∧ Summable (fun j => I j / E (2 ^ (j + 1))) ∧ (∀ j, u (2 ^ (j + 1)) ≤ (2 : ℝ) ^ d * u (2 ^ j) + I j * c) ∧ (∀ j, |(2 : ℝ) ^ d * E (2 ^ j) - E (2 ^ (j + 1))| ≤ I j)) := by
-- proof
  apply StatMech.FK.bxt_negLogDoublingBound_satisfiable d

/--
[bxt_fk_uniqueness_of_doubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean)
-/
@[path]
private lemma bxt_fk_uniqueness_of_doubling_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {osc : ℝ → ℕ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hdoubling : ∀ t, bxt_NegLogDoublingBound d t)
  (hbdd : ∀ t, ∃ M : ℝ, ∀ j, |bxt_u d t (2 ^ j) / bxt_E d (2 ^ j)| ≤ M)
  (hosc : ∀ t, Tendsto (osc t) atTop (𝓝 0))
  (hsand : ∀ t, ∀ n, 1 ≤ n → |ivp2_tiltFreeEnergy (boxGraph d n) 2 t - ivp2_tiltFreeEnergy (boxGraph d (2 ^ (Nat.log 2 n))) 2 t| ≤ osc t (Nat.log 2 n))
  (hfreeRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
  (hwiredRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.bxt_fk_uniqueness_of_doubling hd N eb hEbox hdoubling hbdd osc hosc hsand hfreeRot hwiredRot

/--
[bxt_residue_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTiling.lean)
-/
@[path]
private lemma bxt_residue_remark_eq
  {d : ℕ} :
-- imply
  True := by
-- proof
  apply StatMech.FK.bxt_residue_remark


-- created on 2026-10-23
