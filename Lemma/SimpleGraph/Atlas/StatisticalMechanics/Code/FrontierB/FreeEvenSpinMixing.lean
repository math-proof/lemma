import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenSpinMixing.Part3
open Filter MeasureTheory Set Topology Function StatMech StatMech.FrontierB


/--
[freeInfiniteVolume_eventPairCorrelationAverage_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean)
-/
@[path]
private lemma freeInfiniteVolume_eventPairCorrelationAverage_tendsto_eq
  {d : Nat}
  {p : Real}
  {A B : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA : MeasurableSet A)
  (hB : MeasurableSet B) :
-- imply
  let mu := (freeInfiniteVolume d hp hp1 (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n, mu.real (A ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' B)) atTop (nhds (mu.real A * mu.real B)) := by
-- proof
  apply StatMech.FrontierB.freeInfiniteVolume_eventPairCorrelationAverage_tendsto hd hp hp1 A B hA hB

/--
[markReachableCount_shift_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean)
-/
@[path]
private lemma markReachableCount_shift_eq_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {omega : ConfigSpace (Sym2 (Site d))}
  {A : Finset (Site d)}
  {x : Site d} :
-- imply
  markReachableCount (hypercubicLattice d) (shift g omega) A x = markReachableCount (hypercubicLattice d) omega (A.image fun y => g⁻¹ • y) (g⁻¹ • x) := by
-- proof
  apply StatMech.FrontierB.markReachableCount_shift_eq g omega A x

/--
[allClustersEven_shift_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean)
-/
@[path]
private lemma allClustersEven_shift_iff_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {omega : ConfigSpace (Sym2 (Site d))}
  {A : Finset (Site d)} :
-- imply
  AllClustersEven (hypercubicLattice d) (shift g omega) A ↔ AllClustersEven (hypercubicLattice d) omega (A.image fun x => g⁻¹ • x) := by
-- proof
  apply StatMech.FrontierB.allClustersEven_shift_iff g omega A

/--
[preimage_allClustersEvenEvent_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean)
-/
@[path]
private lemma preimage_allClustersEvenEvent_shift_eq
  {d : Nat}
  {g : Multiplicative (Site d)}
  {A : Finset (Site d)} :
-- imply
  shift g ⁻¹' allClustersEvenEvent (hypercubicLattice d) A = allClustersEvenEvent (hypercubicLattice d) (A.image fun x => g⁻¹ • x) := by
-- proof
  apply StatMech.FrontierB.preimage_allClustersEvenEvent_shift g A

/--
[freeEvenParityGap_average_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean)
-/
@[path]
private lemma freeEvenParityGap_average_tendsto_zero_eq
  {d : Nat}
  {p : Real}
  {A B : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hAeven : Even A.card)
  (hBeven : Even B.card) :
-- imply
  let mu := (freeInfiniteVolume d hp hp1 (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n, freeEvenParityGap hd mu A B k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierB.freeEvenParityGap_average_tendsto_zero hd hp hp1 A B hAeven hBeven

/--
[freeState_spinProd_gks_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean)
-/
@[path]
private lemma freeState_spinProd_gks_second_eq
  {d : Nat}
  {d : Nat}
  {beta : Real}
  {A B : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  (∫ sigma, spinProd A sigma ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) * (∫ sigma, spinProd B sigma ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) ≤ ∫ sigma, spinProd (A ∆ B) sigma ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.freeState_spinProd_gks_second d beta hbeta A B

/--
[freeEvenParityMass_gap_nonneg_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean)
-/
@[path]
private lemma freeEvenParityMass_gap_nonneg_of_disjoint_eq
  {d : Nat}
  {beta : Real}
  {A B : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hAeven : Even A.card)
  (hBeven : Even B.card)
  (hdisj : Disjoint A B) :
-- imply
  let mu := (freeInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] linarith) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure _) 0 ≤ mu.real (allClustersEvenEvent (hypercubicLattice d) (A ∪ B)) - mu.real (allClustersEvenEvent (hypercubicLattice d) A) * mu.real (allClustersEvenEvent (hypercubicLattice d) B) := by
-- proof
  apply StatMech.FrontierB.freeEvenParityMass_gap_nonneg_of_disjoint hd hbeta A B hAeven hBeven hdisj

/--
[freeInfiniteVolume_evenParity_family_pairMixing_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean)
-/
@[path]
private lemma freeInfiniteVolume_evenParity_family_pairMixing_after_eq
  {d : Nat}
  {beta : Real}
  {K : Nat}
  {supports : Finset (Finset (Site d))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (heven : ∀ A ∈ supports, Even A.card)
  (hepsilon : 0 < epsilon) :
-- imply
  let p := 1 - Real.exp (-2 * beta) let mu := (freeInfiniteVolume d (p := p) (q := 2) (by dsimp [p] apply sub_pos.mpr rw [Real.exp_lt_one_iff] linarith) (by dsimp [p] linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure _) ∃ k : Nat, K ≤ k ∧ ∀ A ∈ supports, ∀ B ∈ supports, Disjoint A (B.image fun x => (FK.freeAxisTranslationPower hd k)⁻¹ • x) ∧ abs (mu.real (allClustersEvenEvent (hypercubicLattice d) (A ∪ B.image fun x => (FK.freeAxisTranslationPower hd k)⁻¹ • x)) - mu.real (allClustersEvenEvent (hypercubicLattice d) A) * mu.real (allClustersEvenEvent (hypercubicLattice d) B)) < epsilon := by
-- proof
  apply StatMech.FrontierB.freeInfiniteVolume_evenParity_family_pairMixing_after hd hbeta K supports heven epsilon hepsilon

/--
[freeInfiniteVolume_evenParity_family_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean)
-/
@[path]
private lemma freeInfiniteVolume_evenParity_family_pairMixing_eq
  {d : Nat}
  {beta : Real}
  {supports : Finset (Finset (Site d))}
  {epsilon : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (heven : ∀ A ∈ supports, Even A.card)
  (hepsilon : 0 < epsilon) :
-- imply
  let p := 1 - Real.exp (-2 * beta) let mu := (freeInfiniteVolume d (p := p) (q := 2) (by dsimp [p] apply sub_pos.mpr rw [Real.exp_lt_one_iff] linarith) (by dsimp [p] linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure _) ∃ g : Multiplicative (Site d), ∀ A ∈ supports, ∀ B ∈ supports, Disjoint A (B.image fun x => g⁻¹ • x) ∧ abs (mu.real (allClustersEvenEvent (hypercubicLattice d) (A ∪ B.image fun x => g⁻¹ • x)) - mu.real (allClustersEvenEvent (hypercubicLattice d) A) * mu.real (allClustersEvenEvent (hypercubicLattice d) B)) < epsilon := by
-- proof
  apply StatMech.FrontierB.freeInfiniteVolume_evenParity_family_pairMixing hd hbeta supports heven epsilon hepsilon


-- created on 2026-10-23
