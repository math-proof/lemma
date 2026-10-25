import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangThermodynamicPrereq.Part2
open Filter Set Topology StatMech StatMech.FrontierA


/--
[finiteFerromagneticLeeYang_headline](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangThermodynamicPrereq.lean)
-/
@[path]
private lemma finiteFerromagneticLeeYang_headline_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  (∀ z : ℂ, (leeYangComplexPolynomial G beta).eval z = 0 → ‖z‖ = 1) ∧ (∀ z : ℂ, ‖z‖ ≠ 1 → (leeYangComplexPolynomial G beta).eval z ≠ 0) ∧ (∀ h : ℂ, h.re ≠ 0 → leeYangComplexFieldPartition G beta h ≠ 0) ∧ ∀ f : ConfigSpace V → ℂ, AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f) {h : ℂ | h.re ≠ 0} := by
-- proof
  apply StatMech.FrontierA.finiteFerromagneticLeeYang_headline hbeta

/--
[continuousOn_leeYangRightHalfPlaneDerivativeBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangThermodynamicPrereq.lean)
-/
@[path]
private lemma continuousOn_leeYangRightHalfPlaneDerivativeBound_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  ContinuousOn (leeYangRightHalfPlaneDerivativeBound beta) {h : ℂ | 0 < h.re} := by
-- proof
  apply StatMech.FrontierA.continuousOn_leeYangRightHalfPlaneDerivativeBound hbeta

/--
[continuousOn_leeYangLeftHalfPlaneDerivativeBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangThermodynamicPrereq.lean)
-/
@[path]
private lemma continuousOn_leeYangLeftHalfPlaneDerivativeBound_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  ContinuousOn (leeYangLeftHalfPlaneDerivativeBound beta) {h : ℂ | h.re < 0} := by
-- proof
  apply StatMech.FrontierA.continuousOn_leeYangLeftHalfPlaneDerivativeBound hbeta

/--
[leeYangBox_normalizedFieldLogDerivative_boundedOn_compact_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangThermodynamicPrereq.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_boundedOn_compact_rightHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {beta : ℝ}
  {K : Set ℂ}
-- given
  (hbeta : 0 < beta)
  (hK : IsCompact K)
  (hKright : K ⊆ {h : ℂ | 0 < h.re}) :
-- imply
  ∃ C : ℝ, ∀ (n : ℕ) (h : ℂ), h ∈ K → ‖leeYangNormalizedFieldLogDerivative (boxGraph d n) beta h‖ ≤ C := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_boundedOn_compact_rightHalfPlane d hbeta hK hKright

/--
[leeYangBox_normalizedFieldLogDerivative_boundedOn_compact_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangThermodynamicPrereq.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_boundedOn_compact_leftHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {beta : ℝ}
  {K : Set ℂ}
-- given
  (hbeta : 0 < beta)
  (hK : IsCompact K)
  (hKleft : K ⊆ {h : ℂ | h.re < 0}) :
-- imply
  ∃ C : ℝ, ∀ (n : ℕ) (h : ℂ), h ∈ K → ‖leeYangNormalizedFieldLogDerivative (boxGraph d n) beta h‖ ≤ C := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_boundedOn_compact_leftHalfPlane d hbeta hK hKleft

/--
[leeYangBox_normalizedFieldLogDerivative_normalFamilyData_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangThermodynamicPrereq.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_normalFamilyData_rightHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  (∀ n, DifferentiableOn ℂ (leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) {h : ℂ | 0 < h.re}) ∧ ∀ (K : Set ℂ), IsCompact K → K ⊆ {h : ℂ | 0 < h.re} → ∃ C : ℝ, ∀ (n : ℕ) (h : ℂ), h ∈ K → ‖leeYangNormalizedFieldLogDerivative (boxGraph d n) beta h‖ ≤ C := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_normalFamilyData_rightHalfPlane d hbeta

/--
[leeYangBox_normalizedFieldLogDerivative_normalFamilyData_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangThermodynamicPrereq.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_normalFamilyData_leftHalfPlane_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  (∀ n, DifferentiableOn ℂ (leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) {h : ℂ | h.re < 0}) ∧ ∀ (K : Set ℂ), IsCompact K → K ⊆ {h : ℂ | h.re < 0} → ∃ C : ℝ, ∀ (n : ℕ) (h : ℂ), h ∈ K → ‖leeYangNormalizedFieldLogDerivative (boxGraph d n) beta h‖ ≤ C := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_normalFamilyData_leftHalfPlane d hbeta


-- created on 2026-10-23
