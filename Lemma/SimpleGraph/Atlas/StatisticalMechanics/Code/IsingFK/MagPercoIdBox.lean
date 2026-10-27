import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
open MeasureTheory Filter Topology StatMech StatMech.IsingFK


/--
[origin_mem_box_boxVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean)
-/
@[path]
private lemma origin_mem_box_boxVerts_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  origin d ∈ box d n := by
-- proof
  apply StatMech.IsingFK.origin_mem_box_boxVerts d n

/--
[boxBoundary_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean)
-/
@[path]
private lemma boxBoundary_nonempty_eq
  {d : ℕ}
  {d n : ℕ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  ∃ v : boxVerts d n, boxBoundary d n v := by
-- proof
  apply StatMech.IsingFK.boxBoundary_nonempty d n hd hn

/--
[fvMagnetization_eq_boxBoundaryConnProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean)
-/
@[path]
private lemma fvMagnetization_eq_boxBoundaryConnProfile_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {p : ℝ}
  {n : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : (0 : ℝ) < 2)
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hisingBox : fvMagnetization d β n = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) p (boxOrigin d n)) :
-- imply
  fvMagnetization d β n = boxBoundaryConnProfile d hp hp1 hq n := by
-- proof
  apply StatMech.IsingFK.fvMagnetization_eq_boxBoundaryConnProfile d β hp hp1 hq hd hn hisingBox

/--
[magPercoIdBox_of_fvES_of_fkLim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean)
-/
@[path]
private lemma magPercoIdBox_of_fvES_of_fkLim_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : (0 : ℝ) < 2)
  (hd : 1 ≤ d)
  (hisingBox : ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) p (boxOrigin d n))
  (hfkLimBox : Tendsto (fun n => boxBoundaryConnProfile d hp hp1 hq n) atTop (𝓝 (FK.fkTheta d hp hp1 hq (q := 2)))) :
-- imply
  magnetization d β = FK.fkTheta d hp hp1 hq (q := 2) := by
-- proof
  apply StatMech.IsingFK.magPercoIdBox_of_fvES_of_fkLim d β hp hp1 hq hd hisingBox hfkLimBox

/--
[magPercoIdBox_final](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean)
-/
@[path]
private lemma magPercoIdBox_final_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) (pOfBeta β) (boxOrigin d n))
  (hfkLimBox : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), Tendsto (fun n => boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n) atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))) :
-- imply
  ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
-- proof
  apply StatMech.IsingFK.magPercoIdBox_final d hd hisingBox hfkLimBox

/--
[ising_transition_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean)
-/
@[path]
private lemma ising_transition_box_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) (pOfBeta β) (boxOrigin d n))
  (hfkLimBox : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), Tendsto (fun n => boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n) atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧ (∀ β, βc < β → 0 < magnetization d β) := by
-- proof
  apply StatMech.IsingFK.ising_transition_box d hd hisingBox hfkLimBox hFKsub hpc1

/--
[isingBetaC_eq_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean)
-/
@[path]
private lemma isingBetaC_eq_box_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d n) (boxBoundary d n) (0 : Fin 2) (pOfBeta β) (boxOrigin d n))
  (hfkLimBox : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), Tendsto (fun n => boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n) atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
-- proof
  apply StatMech.IsingFK.isingBetaC_eq_box d hd hisingBox hfkLimBox hFKsub hpc1


-- created on 2026-10-23
