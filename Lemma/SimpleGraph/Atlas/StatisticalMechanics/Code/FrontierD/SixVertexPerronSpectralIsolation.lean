import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexPerronSpectralIsolation
open Finset Filter Matrix Topology StatMech StatMech.FrontierD


/--
[hermitian_trace_sq_eq_sum_eigenvalues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma hermitian_trace_sq_eq_sum_eigenvalues_eq
  [Fintype α]
  [DecidableEq α]
  {A : Matrix α α Real}
-- given
  (hA : A.IsHermitian) :
-- imply
  Matrix.trace (A ^ 2) = ∑ i : Fin (Fintype.card α), hA.eigenvalues₀ i ^ 2 := by
-- proof
  apply StatMech.FrontierD.hermitian_trace_sq_eq_sum_eigenvalues A hA

/--
[hermitian_three_eigenvalues_sq_le_trace_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma hermitian_three_eigenvalues_sq_le_trace_sq_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α Real}
  {a b d : Real}
-- given
  (hA : A.IsHermitian)
  (ha : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) a)
  (hb : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) b)
  (hd : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) d)
  (hab : a ≠ b)
  (had : a ≠ d)
  (hbd : b ≠ d) :
-- imply
  a ^ 2 + b ^ 2 + d ^ 2 ≤ Matrix.trace (A ^ 2) := by
-- proof
  apply StatMech.FrontierD.hermitian_three_eigenvalues_sq_le_trace_sq A hA ha hb hd hab had hbd

/--
[exists_eigenvalue_le_rayleigh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma exists_eigenvalue_le_rayleigh_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α Real}
  {v : EuclideanSpace Real α}
-- given
  (hA : A.IsHermitian)
  (hv : v ≠ 0) :
-- imply
  ∃ μ : Real, Module.End.HasEigenvalue (Matrix.toEuclideanLin A) μ ∧ μ ≤ @RCLike.re Real _ (inner Real (Matrix.toEuclideanLin A v) v) / ‖v‖ ^ 2 := by
-- proof
  apply StatMech.FrontierD.exists_eigenvalue_le_rayleigh A hA v hv

/--
[sixVertexSectorTransferNormalized_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma sixVertexSectorTransferNormalized_isHermitian_eq
  {N n : Nat}
  {c : Real} :
-- imply
  (sixVertexSectorTransferNormalized N n c).IsHermitian := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferNormalized_isHermitian N n c

/--
[sixVertexSectorTransferNormalized_hasEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma sixVertexSectorTransferNormalized_hasEigenvalue_eq
  {N n : Nat}
  {c μ : Real}
-- given
  (hscale : (c ^ 2 - 2) ^ n ≠ 0)
  (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) μ) :
-- imply
  Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized N n c)) (μ / (c ^ 2 - 2) ^ n) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferNormalized_hasEigenvalue hscale hμ

/--
[sixVertexSectorTransferNormalized_top_hasEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma sixVertexSectorTransferNormalized_top_hasEigenvalue_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : n ≤ N)
  (hscale : (c ^ 2 - 2) ^ n ≠ 0) :
-- imply
  Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized N n c)) (sixVertexSectorTopEigenvalue N n hn c / (c ^ 2 - 2) ^ n) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferNormalized_top_hasEigenvalue hn hscale

/--
[tendsto_trace_sixVertexSectorTransferNormalized_sq_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma tendsto_trace_sixVertexSectorTransferNormalized_sq_half_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  Tendsto (fun c => Matrix.trace (sixVertexSectorTransferNormalized N n c ^ 2)) atTop (nhds 2) := by
-- proof
  apply StatMech.FrontierD.tendsto_trace_sixVertexSectorTransferNormalized_sq_half hn hhalf

/--
[sixVertexSectorTransfer_alternatingDifference_rayleigh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_alternatingDifference_rayleigh_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  let even := sixVertexAlternatingEvenSector N n hhalf.le let odd := sixVertexAlternatingOddSector N n hhalf.le let v : SixVertexSector N n → Real := fun x => if x = even then 1 else if x = odd then -1 else 0 (∑ x, v x * (sixVertexSectorTransfer N n c *ᵥ v) x) / (∑ x, v x ^ 2) = 2 - c ^ (2 * n) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_alternatingDifference_rayleigh hn hhalf c

/--
[tendsto_sixVertexSectorTransfer_alternatingDifference_rayleigh_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma tendsto_sixVertexSectorTransfer_alternatingDifference_rayleigh_half_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Tendsto (fun c : Real => (2 - c ^ (2 * n)) / (c ^ 2 - 2) ^ n) atTop (nhds (-1)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexSectorTransfer_alternatingDifference_rayleigh_half hn

/--
[exists_sixVertexSectorTransferNormalized_eigenvalue_le_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma exists_sixVertexSectorTransferNormalized_eigenvalue_le_alternating_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N)
  (hscale : (c ^ 2 - 2) ^ n ≠ 0) :
-- imply
  ∃ μ : Real, Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized N n c)) μ ∧ μ ≤ (2 - c ^ (2 * n)) / (c ^ 2 - 2) ^ n := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexSectorTransferNormalized_eigenvalue_le_alternating hn hhalf hscale

/--
[eventually_eq_sixVertexSectorTop_normalized_of_positive_eigenvalue_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronSpectralIsolation.lean)
-/
@[path]
private lemma eventually_eq_sixVertexSectorTop_normalized_of_positive_eigenvalue_half_eq
  {N n : Nat}
  {μ : Real → Real}
  {δ : Real}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N)
  (hδ : 0 < δ)
  (hμeig : ∀ᶠ c : Real in atTop, Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized N n c)) (μ c))
  (hμlower : ∀ᶠ c : Real in atTop, δ ≤ μ c) :
-- imply
  ∀ᶠ c : Real in atTop, μ c = sixVertexSectorTopEigenvalue N n (by omega) c / (c ^ 2 - 2) ^ n := by
-- proof
  apply StatMech.FrontierD.eventually_eq_sixVertexSectorTop_normalized_of_positive_eigenvalue_half hn hhalf μ hδ hμeig hμlower


-- created on 2026-10-23
