import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexFiniteRegion
open StatMech StatMech.Universality StatMech.Universality.HexFiniteRegion


/--
[vertices_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma vertices_mem_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
-- imply
  ∀ x ∈ (ofTurns a h0 ts).vertices, x ∈ R.verts := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.vertices_mem R a h0 ts hstay

/--
[numVertices_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma numVertices_le_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 ts).IsSAW)
  (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
-- imply
  ts.length + 1 ≤ R.verts.card := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.numVertices_le R a h0 ts hsaw hstay

/--
[length_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma length_lt_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (ofTurns a h0 ts).IsSAW)
  (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
-- imply
  ts.length < R.verts.card := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.length_lt R a h0 ts hsaw hstay

/--
[hexFinite_boundedLegal_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma hexFinite_boundedLegal_finite_eq
  {N : ℕ} :
-- imply
  {ts : List ℤ | (∀ t ∈ ts, t = 1 ∨ t = -1) ∧ ts.length ≤ N}.Finite := by
-- proof
  apply StatMech.Universality.hexFinite_boundedLegal_finite N

/--
[support_isLegalSAW_staysIn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma support_isLegalSAW_staysIn_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0)
  (h : ts ∈ Function.support (combinedSummand R.inRegion a h0 v du)) :
-- imply
  (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn R.inRegion := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.support_isLegalSAW_staysIn R hdu ts h

/--
[support_subset_boundedLegal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma support_subset_boundedLegal_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
-- given
  (hdu : du ≠ 0) :
-- imply
  Function.support (combinedSummand R.inRegion a h0 v du) ⊆ {ts : List ℤ | (∀ t ∈ ts, t = 1 ∨ t = -1) ∧ ts.length ≤ R.verts.card} := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.support_subset_boundedLegal R hdu

/--
[support_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma support_finite_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
-- given
  (hdu : du ≠ 0) :
-- imply
  (Function.support (combinedSummand R.inRegion a h0 v du)).Finite := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.support_finite R hdu

/--
[mem_supportFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma mem_supportFinset_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {ts : List ℤ}
-- given
  (hdu : du ≠ 0) :
-- imply
  ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu ↔ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.mem_supportFinset R hdu ts

/--
[classify_p_from_covering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma classify_p_from_covering_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {triplets : Finset ℕ}
  {tripBase : ℕ → List ℤ}
-- given
  (covp : ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), (ofTurns a h0 ts).EndsAt (v + du) → ∃ T ∈ triplets, tripBase T = ts) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), (ofTurns a h0 ts).EndsAt (v + du) → ∃ T : ℕ, T ∈ triplets ∧ tripBase T = ts := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.classify_p_from_covering R triplets tripBase covp

/--
[classify_q_from_covering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma classify_q_from_covering_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {pairs triplets : Finset ℕ}
  {pairBase pairLq tripBase : ℕ → List ℤ}
-- given
  (covq : ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → (∃ T ∈ triplets, tripBase T ++ [-1] = ts) ∨ (∃ P ∈ pairs, pairBase P ++ pairLq P = ts)) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [-1] = ts) ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLq P = ts) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.classify_q_from_covering R pairs triplets pairBase pairLq tripBase covq

/--
[classify_r_from_covering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma classify_r_from_covering_eq
  {R : HexFiniteRegion}
  {a : ℂ}
  {h0 : ℤ}
  {v du : ℂ}
  {pairs triplets : Finset ℕ}
  {pairBase pairLr tripBase : ℕ → List ℤ}
-- given
  (covr : ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → (∃ T ∈ triplets, tripBase T ++ [1] = ts) ∨ (∃ P ∈ pairs, pairBase P ++ pairLr P = ts)) :
-- imply
  ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du), (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [1] = ts) ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLr P = ts) := by
-- proof
  apply StatMech.Universality.HexFiniteRegion.classify_r_from_covering R pairs triplets pairBase pairLr tripBase covr

/--
[hexFiniteRegion_single_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean)
-/
@[path]
private lemma hexFiniteRegion_single_length_eq
  {a w : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) → ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
  (hsaw : (ofTurns a h0 ts).IsSAW)
  (hstay : (ofTurns a h0 ts).StaysIn (hexFiniteRegion_single a w hclosure).inRegion) :
-- imply
  ts = [] := by
-- proof
  apply StatMech.Universality.hexFiniteRegion_single_length a w h0 ts hclosure hsaw hstay


-- created on 2026-10-23
