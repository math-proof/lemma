import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferPerron.Part2
open Finset Matrix Filter Topology StatMech StatMech.Ising


/--
[positiveTransfer_isPerronFrobenius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean)
-/
@[path]
private lemma positiveTransfer_isPerronFrobenius_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j) :
-- imply
  0 < positiveTransferTopEigenvalue A hHerm ∧ (exists v : EuclideanSpace Real alpha, (forall i, 0 < v i) ∧ A *ᵥ (fun i => v i) = positiveTransferTopEigenvalue A hHerm • (fun i => v i)) ∧ Module.finrank Real (Module.End.eigenspace (Matrix.toEuclideanLin A) (positiveTransferTopEigenvalue A hHerm)) = 1 ∧ forall mu : Real, Module.End.HasEigenvalue (Matrix.toEuclideanLin A) mu -> mu ≠ positiveTransferTopEigenvalue A hHerm -> := by
-- proof
  apply StatMech.Ising.positiveTransfer_isPerronFrobenius A hHerm hpos

/--
[positiveTransfer_positive_eigenvalue_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean)
-/
@[path]
private lemma positiveTransfer_positive_eigenvalue_eq_top_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
  {lam : Real}
  {u : EuclideanSpace Real alpha}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j)
  (hupos : forall i, 0 < u i)
  (hueig : A *ᵥ (fun i => u i) = lam • (fun i => u i)) :
-- imply
  lam = positiveTransferTopEigenvalue A hHerm := by
-- proof
  apply StatMech.Ising.positiveTransfer_positive_eigenvalue_eq_top A hHerm hpos hupos hueig

/--
[positiveTransfer_positive_unit_eigenvector_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean)
-/
@[path]
private lemma positiveTransfer_positive_unit_eigenvector_unique_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
  {lam mu : Real}
  {u v : EuclideanSpace Real alpha}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j)
  (hupos : forall i, 0 < u i)
  (hvpos : forall i, 0 < v i)
  (hunorm : norm u = 1)
  (hvnorm : norm v = 1)
  (hueig : A *ᵥ (fun i => u i) = lam • (fun i => u i))
  (hveig : A *ᵥ (fun i => v i) = mu • (fun i => v i)) :
-- imply
  u = v := by
-- proof
  apply StatMech.Ising.positiveTransfer_positive_unit_eigenvector_unique A hHerm hpos hupos hvpos hunorm hvnorm hueig hveig

/--
[positiveTransfer_normalized_mulVec_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean)
-/
@[path]
private lemma positiveTransfer_normalized_mulVec_tendsto_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j)
  (a : alpha -> Real)
  (ha : forall i, 0 < a i) :
-- imply
  exists lam : Real, 0 < lam ∧ exists u : EuclideanSpace Real alpha, (forall i, 0 < u i) ∧ norm u = 1 ∧ A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧ exists c : Real, 0 < c ∧ Tendsto (fun n : Nat => WithLp.toLp 2 (fun i => ((A ^ n) *ᵥ a) i / lam ^ n)) atTop (nhds (c • u)) := by
-- proof
  apply StatMech.Ising.positiveTransfer_normalized_mulVec_tendsto A hHerm hpos a ha

/--
[positiveTransfer_normalized_mulVec_tendsto_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean)
-/
@[path]
private lemma positiveTransfer_normalized_mulVec_tendsto_apply_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j)
  (a : alpha -> Real)
  (ha : forall i, 0 < a i) :
-- imply
  exists lam : Real, 0 < lam ∧ exists u : EuclideanSpace Real alpha, (forall i, 0 < u i) ∧ norm u = 1 ∧ A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧ exists c : Real, 0 < c ∧ forall i, Tendsto (fun n : Nat => ((A ^ n) *ᵥ a) i / lam ^ n) atTop (nhds (c * u i)) := by
-- proof
  apply StatMech.Ising.positiveTransfer_normalized_mulVec_tendsto_apply A hHerm hpos a ha

/--
[positiveTransfer_normalized_mulVec_pair_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean)
-/
@[path]
private lemma positiveTransfer_normalized_mulVec_pair_tendsto_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j)
  (a b : alpha -> Real)
  (ha : forall i, 0 < a i)
  (hb : forall i, 0 < b i) :
-- imply
  exists lam : Real, 0 < lam ∧ exists u : EuclideanSpace Real alpha, (forall i, 0 < u i) ∧ norm u = 1 ∧ A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧ exists ca cb : Real, 0 < ca ∧ 0 < cb ∧ Tendsto (fun n : Nat => WithLp.toLp 2 (fun i => ((A ^ n) *ᵥ a) i / lam ^ n)) atTop (nhds (ca • u)) ∧ Tendsto (fun n : Nat => WithLp.toLp 2 (fun i => ((A ^ n) *ᵥ b) i / lam ^ n)) atTop (nhds (cb • u)) := by
-- proof
  apply StatMech.Ising.positiveTransfer_normalized_mulVec_pair_tendsto A hHerm hpos a b ha hb

/--
[positiveTransfer_normalized_dotProduct_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean)
-/
@[path]
private lemma positiveTransfer_normalized_dotProduct_tendsto_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j)
  (a : alpha -> Real)
  (ha : forall i, 0 < a i)
  (ell : alpha -> Real) :
-- imply
  exists lam : Real, 0 < lam ∧ exists u : EuclideanSpace Real alpha, (forall i, 0 < u i) ∧ norm u = 1 ∧ A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧ exists c : Real, 0 < c ∧ Tendsto (fun n : Nat => ∑ i, ell i * (((A ^ n) *ᵥ a) i / lam ^ n)) atTop (nhds (c * ∑ i, ell i * u i)) := by
-- proof
  apply StatMech.Ising.positiveTransfer_normalized_dotProduct_tendsto A hHerm hpos a ha ell

/--
[positiveTransfer_log_dotProduct_div_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean)
-/
@[path]
private lemma positiveTransfer_log_dotProduct_div_tendsto_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A : Matrix alpha alpha Real}
-- given
  (hHerm : A.IsHermitian)
  (hpos : forall i j, 0 < A i j)
  (a ell : alpha -> Real)
  (ha : forall i, 0 < a i)
  (hell : forall i, 0 < ell i) :
-- imply
  exists lam : Real, 0 < lam ∧ Tendsto (fun n : Nat => Real.log (∑ i, ell i * ((A ^ n) *ᵥ a) i) / (n : Real)) atTop (nhds (Real.log lam)) := by
-- proof
  apply StatMech.Ising.positiveTransfer_log_dotProduct_div_tendsto A hHerm hpos a ell ha hell

/--
[positiveTransfer_log_dotProduct_sub_div_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PositiveTransferPerron.lean)
-/
@[path]
private lemma positiveTransfer_log_dotProduct_sub_div_tendsto_eq
  [Fintype alpha]
  [DecidableEq alpha]
  [Nonempty alpha]
  {A B : Matrix alpha alpha Real}
-- given
  (hAHerm : A.IsHermitian)
  (hBHerm : B.IsHermitian)
  (hApos : forall i j, 0 < A i j)
  (hBpos : forall i j, 0 < B i j)
  (aA ellA aB ellB : alpha -> Real)
  (haA : forall i, 0 < aA i)
  (hellA : forall i, 0 < ellA i)
  (haB : forall i, 0 < aB i)
  (hellB : forall i, 0 < ellB i) :
-- imply
  exists lamA lamB : Real, 0 < lamA ∧ 0 < lamB ∧ Tendsto (fun n : Nat => (Real.log (∑ i, ellA i * ((A ^ n) *ᵥ aA) i) - Real.log (∑ i, ellB i * ((B ^ n) *ᵥ aB) i)) / (n : Real)) atTop (nhds (Real.log lamA - Real.log lamB)) := by
-- proof
  apply StatMech.Ising.positiveTransfer_log_dotProduct_sub_div_tendsto A B hAHerm hBHerm hApos hBpos aA ellA aB ellB haA hellA haB hellB


-- created on 2026-10-23
