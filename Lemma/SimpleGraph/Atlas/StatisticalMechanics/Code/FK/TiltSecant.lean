import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TiltSecant.Part2
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[secant_exponent_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TiltSecant.lean)
-/
@[path]
private lemma secant_exponent_le_zero_eq
  {q lam m ε : ℝ}
  {S V : ℕ → ℝ}
-- given
  (hq : 1 ≤ q)
  (hlampos : 0 < lam)
  (hlam1 : lam < 1)
  (hε : 0 < ε)
  (hVpos : ∀ n, 0 < V n)
  (hSV : Tendsto (fun n => S n / V n) atTop (𝓝 0))
  (hVinf : Tendsto V atTop atTop)
  (hineq : ∀ n, ε ≤ q ^ (S n) * lam ^ (m * V n) / ε) :
-- imply
  m ≤ 0 := by
-- proof
  apply StatMech.FK.secant_exponent_le_zero hq hlampos hlam1 hε hVpos hSV hVinf hineq

/--
[secant_le_of_per_eps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TiltSecant.lean)
-/
@[path]
private lemma secant_le_of_per_eps_eq
  {a b : ℝ}
-- given
  (h : ∀ ε > 0, b ≤ a + 2 * ε) :
-- imply
  b ≤ a := by
-- proof
  apply StatMech.FK.secant_le_of_per_eps h

/--
[secant_b_le_a_of_finiteVolumeData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TiltSecant.lean)
-/
@[path]
private lemma secant_b_le_a_of_finiteVolumeData_eq
  {q lam a b : ℝ}
  {S V : ℕ → ℝ}
-- given
  (hq : 1 ≤ q)
  (hlampos : 0 < lam)
  (hlam1 : lam < 1)
  (hVpos : ∀ n, 0 < V n)
  (hSV : Tendsto (fun n => S n / V n) atTop (𝓝 0))
  (hVinf : Tendsto V atTop atTop)
  (hfv : ∀ ε > 0, ∀ n, ε ≤ q ^ (S n) * lam ^ ((b - a - 2 * ε) * V n) / ε) :
-- imply
  b ≤ a := by
-- proof
  apply StatMech.FK.secant_b_le_a_of_finiteVolumeData hq hlampos hlam1 hVpos hSV hVinf hfv

/--
[hsecant_discharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TiltSecant.lean)
-/
@[path]
private lemma hsecant_discharged_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hdata : FKSecantData d N eb) :
-- imply
  ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p := by
-- proof
  apply StatMech.FK.hsecant_discharged d N eb hdata

/--
[fk_uniqueness_q2_secant_from_finiteVolumeData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TiltSecant.lean)
-/
@[path]
private lemma fk_uniqueness_q2_secant_from_finiteVolumeData_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hdata : FKSecantData d N eb) :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1) (phi : Measure (ConfigSpace (Sym2 (Site d)))), ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) → phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
-- proof
  apply StatMech.FK.fk_uniqueness_q2_secant_from_finiteVolumeData d N eb hdata


-- created on 2026-10-23
