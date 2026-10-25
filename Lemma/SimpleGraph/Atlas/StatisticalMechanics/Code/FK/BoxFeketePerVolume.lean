import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[bpv_almost_mono_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean)
-/
@[path]
private lemma bpv_almost_mono_converges_eq
  {a δ : ℕ → ℝ}
-- given
  (hδ : ∀ n, 0 ≤ δ n)
  (hsum : Summable δ)
  (hmono : ∀ n, a n - δ n ≤ a (n + 1))
  (hbdd : BddAbove (range a)) :
-- imply
  ∃ L, Tendsto a atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.bpv_almost_mono_converges a δ hδ hsum hmono hbdd

/--
[bpv_nat_log_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean)
-/
@[path]
private lemma bpv_nat_log_tendsto_atTop_eq :
-- imply
  Tendsto (fun n => Nat.log 2 n) atTop atTop := by
-- proof
  apply StatMech.FK.bpv_nat_log_tendsto_atTop

/--
[bpv_full_from_dyadic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean)
-/
@[path]
private lemma bpv_full_from_dyadic_eq
  {a : ℕ → ℝ}
  {L : ℝ}
  {osc : ℕ → ℝ}
-- given
  (hdy : Tendsto (fun j => a (2 ^ j)) atTop (𝓝 L))
  (hosc : Tendsto osc atTop (𝓝 0))
  (hsand : ∀ n, 1 ≤ n → |a n - a (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n)) :
-- imply
  Tendsto a atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.bpv_full_from_dyadic a L hdy osc hosc hsand

/--
[bpv_perVolume_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean)
-/
@[path]
private lemma bpv_perVolume_converges_eq
  {g δ osc : ℕ → ℝ}
-- given
  (hδ : ∀ j, 0 ≤ δ j)
  (hsum : Summable δ)
  (hdymono : ∀ j, g (2 ^ j) - δ j ≤ g (2 ^ (j + 1)))
  (hbdd : BddAbove (range (fun j => g (2 ^ j))))
  (hosc : Tendsto osc atTop (𝓝 0))
  (hsand : ∀ n, 1 ≤ n → |g n - g (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n)) :
-- imply
  ∃ L, Tendsto g atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.bpv_perVolume_converges g δ osc hδ hsum hdymono hbdd hosc hsand

/--
[bpv_boxTiltFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean)
-/
@[path]
private lemma bpv_boxTiltFreeEnergy_tendsto_eq
  {d : ℕ}
  {t : ℝ}
-- given
  (hdata : bpv_PerVolumeFreeEnergyData d t) :
-- imply
  ∃ L : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.bpv_boxTiltFreeEnergy_tendsto t hdata

/--
[bpv_exists_convex_ivPressure_of_perVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean)
-/
@[path]
private lemma bpv_exists_convex_ivPressure_of_perVolume_eq
  {d : ℕ}
-- given
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t) :
-- imply
  ∃ g : ℝ → ℝ, (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t))) ∧ ConvexOn ℝ univ g := by
-- proof
  apply StatMech.FK.bpv_exists_convex_ivPressure_of_perVolume hE hdata

/--
[bpv_perVolumeFreeEnergyData_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean)
-/
@[path]
private lemma bpv_perVolumeFreeEnergyData_satisfiable_eq
  {d : ℕ} :
-- imply
  ∃ (g δ osc : ℕ → ℝ), (∀ j, 0 ≤ δ j) ∧ Summable δ ∧ (∀ j, g (2 ^ j) - δ j ≤ g (2 ^ (j + 1))) ∧ BddAbove (range (fun j => g (2 ^ j))) ∧ Tendsto osc atTop (𝓝 0) ∧ (∀ n, 1 ≤ n → |g n - g (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n)) := by
-- proof
  apply StatMech.FK.bpv_perVolumeFreeEnergyData_satisfiable

/--
[bpv_fk_uniqueness_of_perVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean)
-/
@[path]
private lemma bpv_fk_uniqueness_of_perVolume_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t)
  (hcolfree : ubd_FreeGrowingBoxCollapse (d := d) N)
  (hcolwired : wpd_AvgWiredDensityCollapse (d := d) N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.bpv_fk_uniqueness_of_perVolume hd N eb hEbox hdata hcolfree hcolwired

/--
[bpv_fk_uniqueness_of_perVolume_rotation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean)
-/
@[path]
private lemma bpv_fk_uniqueness_of_perVolume_rotation_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t)
  (hfreeRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
  (hwiredRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.bpv_fk_uniqueness_of_perVolume_rotation hd N eb hEbox hdata hfreeRot hwiredRot

/--
[bpv_residue_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean)
-/
@[path]
private lemma bpv_residue_remark_eq
  {d : ℕ} :
-- imply
  True := by
-- proof
  apply StatMech.FK.bpv_residue_remark


-- created on 2026-10-23
