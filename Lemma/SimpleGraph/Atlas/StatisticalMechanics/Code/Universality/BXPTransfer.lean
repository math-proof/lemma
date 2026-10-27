import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.BXPTransfer.Part2
open MeasureTheory Set StatMech StatMech.Universality


/--
[boxCrossingProbabilities_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean)
-/
@[path]
private lemma boxCrossingProbabilities_nonempty_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
  {n0 : ℕ} :
-- imply
  (boxCrossingProbabilities μ ρ n0).Nonempty := by
-- proof
  apply StatMech.Universality.boxCrossingProbabilities_nonempty μ ρ n0

/--
[boxCrossingProbabilities_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean)
-/
@[path]
private lemma boxCrossingProbabilities_bddBelow_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
  {n0 : ℕ} :
-- imply
  BddBelow (boxCrossingProbabilities μ ρ n0) := by
-- proof
  apply StatMech.Universality.boxCrossingProbabilities_bddBelow μ ρ n0

/--
[boxCrossingProbabilities_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean)
-/
@[path]
private lemma boxCrossingProbabilities_mem_Icc_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {ρ : ℝ}
  {n0 : ℕ}
  {x : ℝ}
-- given
  (hx : x ∈ boxCrossingProbabilities μ ρ n0) :
-- imply
  x ∈ Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Universality.boxCrossingProbabilities_mem_Icc μ ρ n0 hx

/--
[boxCrossingProbabilities_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean)
-/
@[path]
private lemma boxCrossingProbabilities_subset_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
  {n0 n0' : ℕ}
-- given
  (h : n0 ≤ n0') :
-- imply
  boxCrossingProbabilities μ ρ n0' ⊆ boxCrossingProbabilities μ ρ n0 := by
-- proof
  apply StatMech.Universality.boxCrossingProbabilities_subset μ ρ h

/--
[boxCrossingInf_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean)
-/
@[path]
private lemma boxCrossingInf_mono_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
  {n0 n0' : ℕ}
-- given
  (h : n0 ≤ n0') :
-- imply
  boxCrossingInf μ ρ n0 ≤ boxCrossingInf μ ρ n0' := by
-- proof
  apply StatMech.Universality.boxCrossingInf_mono μ ρ h

/--
[bxp_transfer_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean)
-/
@[path]
private lemma bxp_transfer_core_eq
  {μsrc μtgt : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρsrc ρtgt : ℝ}
  {n0src n0tgt : ℕ}
-- given
  (hρ : 1 < ρsrc)
  (htgt : 0 < boxCrossingInf μtgt ρtgt n0tgt)
  (hcmp : ∀ x ∈ boxCrossingProbabilities μsrc ρsrc n0src, ∃ y ∈ boxCrossingProbabilities μtgt ρtgt n0tgt, y ≤ x) :
-- imply
  BoxCrossingProperty μsrc ρsrc := by
-- proof
  apply StatMech.Universality.bxp_transfer_core μsrc μtgt ρsrc ρtgt n0src n0tgt hρ htgt hcmp

/--
[bxp_square_of_triangular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean)
-/
@[path]
private lemma bxp_square_of_triangular_eq
  {μsq μtri : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρsq ρtri : ℝ}
-- given
  (hdata : CrossingTransportData μsq μtri ρsq ρtri)
  (htri : BoxCrossingProperty μtri ρtri) :
-- imply
  BoxCrossingProperty μsq ρsq := by
-- proof
  apply StatMech.Universality.bxp_square_of_triangular hdata htri

/--
[bxp_triangular_of_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean)
-/
@[path]
private lemma bxp_triangular_of_square_eq
  {μsq μtri : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρsq ρtri : ℝ}
-- given
  (hdata : CrossingTransportData μsq μtri ρsq ρtri)
  (hsq : BoxCrossingProperty μsq ρsq) :
-- imply
  BoxCrossingProperty μtri ρtri := by
-- proof
  apply StatMech.Universality.bxp_triangular_of_square hdata hsq

/--
[bxp_square_iff_triangular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPTransfer.lean)
-/
@[path]
private lemma bxp_square_iff_triangular_eq
  {μsq μtri : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρsq ρtri : ℝ}
  {p0 p1 p2 : ℝ}
-- given
  (hcrit : IsCriticalTri p0 p1 p2)
  (hdata : CrossingTransportData μsq μtri ρsq ρtri) :
-- imply
  BoxCrossingProperty μsq ρsq ↔ BoxCrossingProperty μtri ρtri := by
-- proof
  apply StatMech.Universality.bxp_square_iff_triangular hcrit hdata


-- created on 2026-10-23
