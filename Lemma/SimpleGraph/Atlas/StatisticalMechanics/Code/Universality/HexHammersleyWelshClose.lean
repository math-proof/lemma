import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexHammersleyWelshClose.Part2
open StatMech StatMech.Universality


/--
[hhw_critFacts_of_finsetBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean)
-/
@[path]
private lemma hhw_critFacts_of_finsetBound_eq
  {f : W → ℝ}
-- given
  (hnn : ∀ w, 0 ≤ f w)
  (hbd : ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1) :
-- imply
  Summable f ∧ (∑' w, f w) ≤ 1 := by
-- proof
  apply StatMech.Universality.hhw_critFacts_of_finsetBound f hnn hbd

/--
[hhw_finsetBound_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean)
-/
@[path]
private lemma hhw_finsetBound_of_boundary_eq
  {f : W → ℝ}
  {cl ct : ℝ}
  {lam tau : Finset W → ℝ}
-- given
  (hcl : 0 ≤ cl)
  (hct : 0 ≤ ct)
  (hlam : ∀ s, 0 ≤ lam s)
  (htau : ∀ s, 0 ≤ tau s)
  (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ s, f w) = 1) :
-- imply
  ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1 := by
-- proof
  apply StatMech.Universality.hhw_finsetBound_of_boundary f cl ct hcl hct lam tau hlam htau hbdry

/--
[hhw_critSummable_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean)
-/
@[path]
private lemma hhw_critSummable_of_boundary_eq
  {f : W → ℝ}
  {cl ct : ℝ}
  {lam tau : Finset W → ℝ}
-- given
  (hcl : 0 ≤ cl)
  (hct : 0 ≤ ct)
  (hlam : ∀ s, 0 ≤ lam s)
  (htau : ∀ s, 0 ≤ tau s)
  (hnn : ∀ w, 0 ≤ f w)
  (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ s, f w) = 1) :
-- imply
  Summable f := by
-- proof
  apply StatMech.Universality.hhw_critSummable_of_boundary f cl ct hcl hct lam tau hlam htau hnn hbdry

/--
[hhw_critLeOne_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean)
-/
@[path]
private lemma hhw_critLeOne_of_boundary_eq
  {f : W → ℝ}
  {cl ct : ℝ}
  {lam tau : Finset W → ℝ}
-- given
  (hcl : 0 ≤ cl)
  (hct : 0 ≤ ct)
  (hlam : ∀ s, 0 ≤ lam s)
  (htau : ∀ s, 0 ≤ tau s)
  (hnn : ∀ w, 0 ≤ f w)
  (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ s, f w) = 1) :
-- imply
  (∑' w, f w) ≤ 1 := by
-- proof
  apply StatMech.Universality.hhw_critLeOne_of_boundary f cl ct hcl hct lam tau hlam htau hnn hbdry

/--
[hhw_finsetBound_of_singleStrip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean)
-/
@[path]
private lemma hhw_finsetBound_of_singleStrip_eq
  {f : W → ℝ}
  {cl ct : ℝ}
  {strip : Finset W → Finset W}
  {lam tau : Finset W → ℝ}
-- given
  (hcl : 0 ≤ cl)
  (hct : 0 ≤ ct)
  (hnn : ∀ w, 0 ≤ f w)
  (hsub : ∀ s, s ⊆ strip s)
  (hlam : ∀ s, 0 ≤ lam s)
  (htau : ∀ s, 0 ≤ tau s)
  (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ strip s, f w) = 1) :
-- imply
  ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1 := by
-- proof
  apply StatMech.Universality.hhw_finsetBound_of_singleStrip f cl ct hcl hct hnn strip hsub lam tau hlam htau hbdry

/--
[hhw_hexColumnOfBoundary_colSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean)
-/
@[path]
private lemma hhw_hexColumnOfBoundary_colSum_eq
  {a : ℂ}
  {T : ℕ}
  (hreach lam tau hlam htau hbdry)
  {y : ℝ}
-- given
  (h0 : ℤ)
  (mem : List ℤ → Prop) :
-- imply
  (hhw_hexColumnOfBoundary a h0 T mem hreach lam tau hlam htau hbdry).colSum y = ∑' w : {ts // mem ts}, y ^ (HexWalk.ofTurns a h0 w.1).numVertices := by
-- proof
  apply StatMech.Universality.hhw_hexColumnOfBoundary_colSum a h0 T mem y

/--
[hhw_hexColumnOfBoundary_critLeOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean)
-/
@[path]
private lemma hhw_hexColumnOfBoundary_critLeOne_eq
  {a : ℂ}
  {T : ℕ}
  (hreach lam tau hlam htau hbdry)
-- given
  (h0 : ℤ)
  (mem : List ℤ → Prop) :
-- imply
  ((hhw_hexColumnOfBoundary a h0 T mem hreach lam tau hlam htau hbdry).colSum hexChiE) ≤ 1 := by
-- proof
  apply StatMech.Universality.hhw_hexColumnOfBoundary_critLeOne a h0 T mem

/--
[hhw_hexColumnOfBoundary_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean)
-/
@[path]
private lemma hhw_hexColumnOfBoundary_nonvacuous_eq
  {a : ℂ}
  {T : ℕ}
-- given
  (h0 : ℤ)
  (hreach : ∀ ts, (fun _ : List ℤ => False) ts → ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re) :
-- imply
  ∃ lam tau : Finset {ts : List ℤ // (fun _ : List ℤ => False) ts} → ℝ, (∀ s, 0 ≤ lam s) ∧ (∀ s, 0 ≤ tau s) ∧ (∀ s : Finset {ts : List ℤ // (fun _ : List ℤ => False) ts}, hexCl * lam s + hexCt * tau s + (∑ w ∈ s, hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices) = 1) := by
-- proof
  apply StatMech.Universality.hhw_hexColumnOfBoundary_nonvacuous a h0 T hreach


-- created on 2026-10-23
