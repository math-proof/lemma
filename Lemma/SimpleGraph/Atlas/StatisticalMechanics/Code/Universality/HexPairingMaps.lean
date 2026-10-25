import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part4
open StatMech StatMech.Universality StatMech.Universality.HexFiniteRegion


/--
[hexPairing_loopReverse_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_loopReverse_pairs_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {Lq : List ℤ}
-- given
  (hLqsum : Lq.sum = -4) :
-- imply
  (loopReverse Lq).sum = 4 ∧ (loopReverse Lq).length = Lq.length ∧ loopReverse (loopReverse Lq) = Lq := by
-- proof
  apply StatMech.Universality.hexPairing_loopReverse_pairs Lq hLqsum

/--
[hexPairing_loopReverse_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_loopReverse_legal_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {Lq : List ℤ}
-- given
  (hLq : ∀ t ∈ Lq, t = 1 ∨ t = -1) :
-- imply
  ∀ t ∈ loopReverse Lq, t = 1 ∨ t = -1 := by
-- proof
  apply StatMech.Universality.hexPairing_loopReverse_legal Lq hLq

/--
[hexPairing_pair_walks_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_pair_walks_ne_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {base Lq : List ℤ}
-- given
  (hLqsum : Lq.sum = -4) :
-- imply
  base ++ Lq ≠ base ++ loopReverse Lq := by
-- proof
  apply StatMech.Universality.hexPairing_pair_walks_ne base Lq hLqsum

/--
[hexPairing_pair_involution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_pair_involution_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {base Lq : List ℤ}
-- given
  (hLqsum : Lq.sum = -4) :
-- imply
  loopReverse (loopReverse Lq) = Lq ∧ base ++ Lq ≠ base ++ loopReverse Lq ∧ (loopReverse Lq).sum = 4 ∧ (loopReverse Lq).length = Lq.length := by
-- proof
  apply StatMech.Universality.hexPairing_pair_involution base Lq hLqsum

/--
[classify_p_of_supportFinset_covering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma classify_p_of_supportFinset_covering_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {triplets : Finset ℕ}
  {tripBase : ℕ → List ℤ}
-- given
  (hdu : du ≠ 0)
  (covp : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu, (ofTurns a h0 ts).EndsAt (v + du) → ∃ T ∈ triplets, tripBase T = ts) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), (ofTurns a h0 ts).EndsAt (v + du) → ∃ T : ℕ, T ∈ triplets ∧ tripBase T = ts := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.classify_p_of_supportFinset_covering R hdu triplets tripBase covp

/--
[classify_q_of_supportFinset_covering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma classify_q_of_supportFinset_covering_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {pairs triplets : Finset ℕ}
  {pairBase pairLq tripBase : ℕ → List ℤ}
-- given
  (hdu : du ≠ 0)
  (covq : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu, (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → (∃ T ∈ triplets, tripBase T ++ [-1] = ts) ∨ (∃ P ∈ pairs, pairBase P ++ pairLq P = ts)) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [-1] = ts) ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLq P = ts) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.classify_q_of_supportFinset_covering R hdu pairs triplets pairBase pairLq tripBase covq

/--
[classify_r_of_supportFinset_covering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma classify_r_of_supportFinset_covering_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {pairs triplets : Finset ℕ}
  {pairBase pairLr tripBase : ℕ → List ℤ}
-- given
  (hdu : du ≠ 0)
  (covr : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu, (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → (∃ T ∈ triplets, tripBase T ++ [1] = ts) ∨ (∃ P ∈ pairs, pairBase P ++ pairLr P = ts)) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [1] = ts) ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLr P = ts) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.classify_r_of_supportFinset_covering R hdu pairs triplets pairBase pairLr tripBase covr

/--
[hexPairing_emptySupport_observable_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_emptySupport_observable_zero_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a w : ℂ}
  {z : ℂ}
  {σ x : ℝ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
  (haz : a ≠ z) :
-- imply
  parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x = 0 := by
-- proof
  apply StatMech.Universality.hexPairing_emptySupport_observable_zero a w h0 z σ x hclosure haz

/--
[hexPairing_emptySupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_emptySupport_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a w : ℂ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
  (hap : a ≠ v + du)
  (haq : a ≠ v + hexOmega * du)
  (har : a ≠ v + hexOmega ^ 2 * du) :
-- imply
  ts ∉ Function.support (combinedSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 v du) := by
-- proof
  apply StatMech.Universality.hexPairing_emptySupport a w h0 v du hdu hclosure hap haq har ts

/--
[hexPairing_vertex_relation_of_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_vertex_relation_of_classification_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {R : HexFiniteRegion}
  {C : HexSawClassification R.inRegion a h0 v du}
-- given
  (hdu : du ≠ 0)
  (hp : Summable fun ts => parafSummand R.inRegion a h0 (v + du) (5/8) hexChi ts)
  (hq : Summable fun ts => parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi ts)
  (hr : Summable fun ts => parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
-- imply
  ((v + du) - v) * parafObservable R.inRegion a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.hexPairing_vertex_relation_of_classification R C hdu hp hq hr

/--
[hexPairing_emptySupport_summand_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_emptySupport_summand_zero_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a w : ℂ}
  {z : ℂ}
  {σ x : ℝ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
  (haz : a ≠ z) :
-- imply
  parafSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x ts = 0 := by
-- proof
  apply StatMech.Universality.hexPairing_emptySupport_summand_zero a w h0 z σ x hclosure haz ts

/--
[hexPairing_emptySupport_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_emptySupport_summable_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a w : ℂ}
  {z : ℂ}
  {σ x : ℝ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
  (haz : a ≠ z) :
-- imply
  Summable fun ts => parafSummand (hexFiniteRegion_single a w hclosure).inRegion a h0 z σ x ts := by
-- proof
  apply StatMech.Universality.hexPairing_emptySupport_summable a w h0 z σ x hclosure haz

/--
[hexPairing_emptySupport_vertex_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_emptySupport_vertex_relation_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a w : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
  (hap : a ≠ v + du)
  (haq : a ≠ v + hexOmega * du)
  (har : a ≠ v + hexOmega ^ 2 * du) :
-- imply
  ((v + du) - v) * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.hexPairing_emptySupport_vertex_relation a w h0 v du hdu hclosure hap haq har

/--
[hexPairing_covering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_covering_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a w : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
  (hap : a ≠ v + du)
  (haq : a ≠ v + hexOmega * du)
  (har : a ≠ v + hexOmega ^ 2 * du) :
-- imply
  (∀ ts ∈ (hexFiniteRegion_single a w hclosure).supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu, (ofTurns a h0 ts).EndsAt (v + du) → ∃ T ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) T = ts) ∧ (∀ ts ∈ (hexFiniteRegion_single a w hclosure).supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu, (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → (∃ T ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) T ++ [-1] = ts) ∨ (∃ P ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) P ++ (fun _ : ℕ => ([] : List ℤ)) P = ts)) ∧ (∀ ts ∈ (hexFiniteRegion_single a w hclosure).supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu, (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → (∃ T ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) T ++ [1] = ts) ∨ (∃ P ∈ (∅ : Finset ℕ), (fun _ : ℕ => ([] : List ℤ)) P ++ (fun _ : ℕ => ([] : List ℤ)) P = ts)) := by
-- proof
  apply StatMech.Universality.hexPairing_covering a w h0 v du hdu hclosure hap haq har

/--
[hexPairing_vertex_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean)
-/
@[path]
private lemma hexPairing_vertex_relation_eq
  {region : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {a w : ℂ}
  {v du : ℂ}
-- given
  (h0 : ℤ)
  (hdu : du ≠ 0)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
  (hap : a ≠ v + du)
  (haq : a ≠ v + hexOmega * du)
  (har : a ≠ v + hexOmega ^ 2 * du) :
-- imply
  ((v + du) - v) * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + du) (5/8) hexChi + ((v + hexOmega * du) - v) * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega * du) (5/8) hexChi + ((v + hexOmega ^ 2 * du) - v) * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
-- proof
  apply StatMech.Universality.hexPairing_vertex_relation a w h0 v du hdu hclosure hap haq har


-- created on 2026-10-23
