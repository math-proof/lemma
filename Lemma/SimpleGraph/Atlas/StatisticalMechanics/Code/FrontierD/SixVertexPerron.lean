import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexSectorPosition_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorPosition_mem_eq
  {N n : ℕ}
  {x : SixVertexSector N n}
  {i : Fin n} :
-- imply
  sixVertexSectorPosition x i ∈ x.val := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_mem x i

/--
[sixVertexSector_upPositions_eq_map_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSector_upPositions_eq_map_position_eq
  {N n : ℕ}
  {x : SixVertexSector N n} :
-- imply
  sixVertexUpPositions (sixVertexSectorRow x) = (List.finRange n).map (sixVertexSectorPosition x) := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_upPositions_eq_map_position x

/--
[sixVertexForwardInterlaced_of_positions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexForwardInterlaced_of_positions_eq
  {N n : ℕ}
  {x y : SixVertexSector N n}
-- given
  (h : SixVertexPositionsForwardInterlaced x y) :
-- imply
  SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) := by
-- proof
  apply StatMech.FrontierD.sixVertexForwardInterlaced_of_positions x y h

/--
[sixVertexSectorPosition_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorPosition_lower_eq
  {N n : ℕ}
  {x : SixVertexSector N n} :
-- imply
  sixVertexSectorPosition (sixVertexLowerSector x) = lowerSectorEmbedding (sixVertexSectorPosition x) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_lower x

/--
[sixVertexLower_positionsForwardInterlaced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexLower_positionsForwardInterlaced_eq
  {N n : ℕ}
  {x : SixVertexSector N n} :
-- imply
  SixVertexPositionsForwardInterlaced (sixVertexLowerSector x) x := by
-- proof
  apply StatMech.FrontierD.sixVertexLower_positionsForwardInterlaced x

/--
[sixVertexLower_interlaced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexLower_interlaced_eq
  {N n : ℕ}
  {x : SixVertexSector N n} :
-- imply
  SixVertexInterlaced (sixVertexSectorRow (sixVertexLowerSector x)) (sixVertexSectorRow x) := by
-- proof
  apply StatMech.FrontierD.sixVertexLower_interlaced x

/--
[sixVertexSectorTransfer_lower_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_lower_pos_eq
  {N n : ℕ}
  {c : ℝ}
  {x : SixVertexSector N n}
-- given
  (hc : 0 < c) :
-- imply
  0 < sixVertexSectorTransfer N n c (sixVertexLowerSector x) x := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_lower_pos hc x

/--
[sixVertexSectorPosition_packed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorPosition_packed_eq
  {N n : ℕ}
-- given
  (hn : n ≤ N) :
-- imply
  sixVertexSectorPosition (sixVertexPackedSector N n hn) = OrderEmbedding.ofStrictMono (Fin.castLE hn) (Fin.strictMono_castLE hn) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_packed N n hn

/--
[sixVertexLower_eq_self_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexLower_eq_self_iff_eq
  {N n : ℕ}
  {x : SixVertexSector N n}
-- given
  (hn : n ≤ N) :
-- imply
  sixVertexLowerSector x = x ↔ x = sixVertexPackedSector N n hn := by
-- proof
  apply StatMech.FrontierD.sixVertexLower_eq_self_iff x hn

/--
[sixVertexSectorHeight_lower_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorHeight_lower_lt_eq
  {N n : ℕ}
  {x : SixVertexSector N n}
-- given
  (hne : sixVertexLowerSector x ≠ x) :
-- imply
  sixVertexSectorHeight (sixVertexLowerSector x) < sixVertexSectorHeight x := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorHeight_lower_lt x hne

/--
[sixVertexSectorTransfer_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_nonneg_eq
  {N n : ℕ}
  {c : ℝ}
  {x y : SixVertexSector N n}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 ≤ sixVertexSectorTransfer N n c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_nonneg hc x y

/--
[sixVertexSectorTransfer_pow_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_pow_nonneg_eq
  {N n k : ℕ}
  {c : ℝ}
  {x y : SixVertexSector N n}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 ≤ (sixVertexSectorTransfer N n c ^ k) x y := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_pow_nonneg hc x y

/--
[sixVertexSectorTransfer_pow_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_pow_symmetric_eq
  {N n k : ℕ}
  {c : ℝ}
  {x y : SixVertexSector N n} :
-- imply
  (sixVertexSectorTransfer N n c ^ k) x y = (sixVertexSectorTransfer N n c ^ k) y x := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_pow_symmetric c x y

/--
[sixVertexSectorTransfer_self_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_self_pos_eq
  {N n : ℕ}
  {c : ℝ}
  {x : SixVertexSector N n} :
-- imply
  0 < sixVertexSectorTransfer N n c x x := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_self_pos c x

/--
[sixVertexSectorTransfer_exists_pow_pos_to_packed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_exists_pow_pos_to_packed_eq
  {N n : ℕ}
  {c : ℝ}
  {x : SixVertexSector N n}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  ∃ k > 0, 0 < (sixVertexSectorTransfer N n c ^ k) x (sixVertexPackedSector N n hn) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_exists_pow_pos_to_packed hn hc x

/--
[sixVertexSectorTransfer_isIrreducible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_isIrreducible_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  (sixVertexSectorTransfer N n c).IsIrreducible := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_isIrreducible hn hc

/--
[sixVertexSectorTransfer_pow_self_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_pow_self_pos_eq
  {N n m : ℕ}
  {c : ℝ}
  {x : SixVertexSector N n}
-- given
  (hc : 0 < c) :
-- imply
  0 < (sixVertexSectorTransfer N n c ^ m) x x := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_pow_self_pos hc x

/--
[sixVertexConnectionExponent_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexConnectionExponent_pos_eq
  {N n : ℕ}
  {c : ℝ}
  {x y : SixVertexSector N n}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  0 < sixVertexConnectionExponent hn hc x y := by
-- proof
  apply StatMech.FrontierD.sixVertexConnectionExponent_pos hn hc x y

/--
[sixVertexConnectionExponent_entry_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexConnectionExponent_entry_pos_eq
  {N n : ℕ}
  {c : ℝ}
  {x y : SixVertexSector N n}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  0 < (sixVertexSectorTransfer N n c ^ sixVertexConnectionExponent hn hc x y) x y := by
-- proof
  apply StatMech.FrontierD.sixVertexConnectionExponent_entry_pos hn hc x y

/--
[sixVertexConnectionExponent_le_primitiveExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexConnectionExponent_le_primitiveExponent_eq
  {N n : ℕ}
  {c : ℝ}
  {x y : SixVertexSector N n}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  sixVertexConnectionExponent hn hc x y ≤ sixVertexPrimitiveExponent N n hn hc := by
-- proof
  apply StatMech.FrontierD.sixVertexConnectionExponent_le_primitiveExponent hn hc x y

/--
[sixVertexPrimitiveExponent_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexPrimitiveExponent_pos_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  0 < sixVertexPrimitiveExponent N n hn hc := by
-- proof
  apply StatMech.FrontierD.sixVertexPrimitiveExponent_pos hn hc

/--
[sixVertexSectorTransfer_primitivePower_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_primitivePower_pos_eq
  {N n : ℕ}
  {c : ℝ}
  {x y : SixVertexSector N n}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  0 < (sixVertexSectorTransfer N n c ^ sixVertexPrimitiveExponent N n hn hc) x y := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_primitivePower_pos hn hc x y

/--
[sixVertexSectorTransfer_isPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_isPrimitive_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  (sixVertexSectorTransfer N n c).IsPrimitive := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_isPrimitive hn hc

/--
[euclideanAbs_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma euclideanAbs_apply_eq
  [Fintype α]
  {v : EuclideanSpace ℝ α}
  {i : α} :
-- imply
  euclideanAbs v i = |v i| := by
-- proof
  apply StatMech.FrontierD.euclideanAbs_apply v i

/--
[norm_euclideanAbs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma norm_euclideanAbs_eq
  [Fintype α]
  {v : EuclideanSpace ℝ α} :
-- imply
  ‖euclideanAbs v‖ = ‖v‖ := by
-- proof
  apply StatMech.FrontierD.norm_euclideanAbs v

/--
[sixVertexSectorTop_exists_nonnegative_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTop_exists_nonnegative_eigenvector_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  ∃ v : EuclideanSpace ℝ (SixVertexSector N n), v ≠ 0 ∧ (∀ i, 0 ≤ v i) ∧ sixVertexSectorTransfer N n c *ᵥ (fun i => v i) = sixVertexSectorTopEigenvalue N n hn c • (fun i => v i) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTop_exists_nonnegative_eigenvector hn hc

/--
[sixVertexSectorTop_exists_positive_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTop_exists_positive_eigenvector_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  ∃ v : EuclideanSpace ℝ (SixVertexSector N n), (∀ i, 0 < v i) ∧ sixVertexSectorTransfer N n c *ᵥ (fun i => v i) = sixVertexSectorTopEigenvalue N n hn c • (fun i => v i) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTop_exists_positive_eigenvector hn hc

/--
[sixVertexSectorTopEigenvalue_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTopEigenvalue_pos_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  0 < sixVertexSectorTopEigenvalue N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTopEigenvalue_pos hn hc

/--
[sixVertexSectorTop_eigenspace_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTop_eigenspace_finrank_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  Module.finrank ℝ (Module.End.eigenspace (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) (sixVertexSectorTopEigenvalue N n hn c)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTop_eigenspace_finrank hn hc

/--
[sixVertexSector_eigenvalue_abs_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSector_eigenvalue_abs_lt_top_eq
  {N n : ℕ}
  {c μ : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c)
  (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) μ)
  (hne : μ ≠ sixVertexSectorTopEigenvalue N n hn c) :
-- imply
  |μ| < sixVertexSectorTopEigenvalue N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_eigenvalue_abs_lt_top hn hc hμ hne

/--
[sixVertexSector_eigenvalue_abs_le_top_of_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSector_eigenvalue_abs_le_top_of_nonzero_eq
  {N n : ℕ}
  {c μ : ℝ}
  {z : EuclideanSpace ℝ (SixVertexSector N n)}
-- given
  (hn : n ≤ N)
  (hc : 0 < c)
  (hzne : z ≠ 0)
  (hzeig : sixVertexSectorTransfer N n c *ᵥ (fun i => z i) = μ • (fun i => z i)) :
-- imply
  |μ| ≤ sixVertexSectorTopEigenvalue N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_eigenvalue_abs_le_top_of_nonzero hn hc hzne hzeig

/--
[sixVertexSectorTop_isPerronFrobenius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexSectorTop_isPerronFrobenius_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  0 < sixVertexSectorTopEigenvalue N n hn c ∧ (∃ v : EuclideanSpace ℝ (SixVertexSector N n), (∀ i, 0 < v i) ∧ sixVertexSectorTransfer N n c *ᵥ (fun i => v i) = sixVertexSectorTopEigenvalue N n hn c • (fun i => v i)) ∧ Module.finrank ℝ (Module.End.eigenspace (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) (sixVertexSectorTopEigenvalue N n hn c)) = 1 ∧ ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) μ → μ ≠ sixVertexSectorTopEigenvalue N n hn c → |μ| < sixVertexSectorTopEigenvalue N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTop_isPerronFrobenius hn hc

/--
[sixVertexLambda_isPerronFrobenius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean)
-/
@[path]
private lemma sixVertexLambda_isPerronFrobenius_eq
  {N r : ℕ}
  {c : ℝ}
-- given
  (hN : Even N)
  (hr : r ≤ N / 2)
  (hc : 0 < c) :
-- imply
  0 < sixVertexLambda N r hN hr c ∧ (∃ v : EuclideanSpace ℝ (SixVertexSector N (N / 2 - r)), (∀ i, 0 < v i) ∧ sixVertexSectorTransfer N (N / 2 - r) c *ᵥ (fun i => v i) = sixVertexLambda N r hN hr c • (fun i => v i)) ∧ Module.finrank ℝ (Module.End.eigenspace (Matrix.toEuclideanLin (sixVertexSectorTransfer N (N / 2 - r) c)) (sixVertexLambda N r hN hr c)) = 1 ∧ ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransfer N (N / 2 - r) c)) μ → μ ≠ sixVertexLambda N r hN hr c → |μ| < sixVertexLambda N r hN hr c := by
-- proof
  apply StatMech.FrontierD.sixVertexLambda_isPerronFrobenius N r hN hr hc


-- created on 2026-10-23
