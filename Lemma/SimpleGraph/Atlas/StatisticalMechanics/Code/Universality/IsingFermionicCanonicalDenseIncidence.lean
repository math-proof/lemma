import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part8
open Filter Set Topology StatMech StatMech.Universality


/--
[fkIsingRationalComplex_denseRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fkIsingRationalComplex_denseRange_eq :
-- imply
  DenseRange fkIsingRationalComplex := by
-- proof
  apply StatMech.Universality.fkIsingRationalComplex_denseRange

/--
[fkIsingRationalPairEnumeration_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fkIsingRationalPairEnumeration_surjective_eq :
-- imply
  Function.Surjective fkIsingRationalPairEnumeration := by
-- proof
  apply StatMech.Universality.fkIsingRationalPairEnumeration_surjective

/--
[fkIsingDenseRationalPoint_denseRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fkIsingDenseRationalPoint_denseRange_eq :
-- imply
  DenseRange fkIsingDenseRationalPoint := by
-- proof
  apply StatMech.Universality.fkIsingDenseRationalPoint_denseRange

/--
[fkIsingSquareInteriorRadialIncidenceOfInt_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialIncidenceOfInt_endpoint_eq
  {n : Nat}
  {x y : Int}
-- given
  (hn : 0 < n)
  (hxy : -(n : Int) ≤ x ∧ x < n ∧ -(n : Int) ≤ y ∧ y < n) :
-- imply
  fkIsingSquareInteriorRadialEndpoint n hn (fkIsingSquareInteriorRadialIncidenceOfInt n hn x y hxy) = fkIsingSquareFullVertexOfInt n x y ⟨hxy.1, le_of_lt hxy.2.1⟩ ⟨hxy.2.2.1, le_of_lt hxy.2.2.2⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialIncidenceOfInt_endpoint n hn x y hxy

/--
[fullSquareScaledVertexEmbedding_fullVertexOfInt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fullSquareScaledVertexEmbedding_fullVertexOfInt_eq
  {n : Nat}
  {scale : Real}
  {x y : Int}
-- given
  (hx : -(n : Int) ≤ x ∧ x ≤ n)
  (hy : -(n : Int) ≤ y ∧ y ≤ n) :
-- imply
  FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding n scale (fkIsingSquareFullVertexOfInt n x y hx hy) = (scale : Complex) * (((x + y : Int) : Real) + ((x - y : Int) : Real) * Complex.I) := by
-- proof
  apply StatMech.Universality.fullSquareScaledVertexEmbedding_fullVertexOfInt n scale x y hx hy

/--
[fkIsing_floor_mul_succ_eventually_in_expandingSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fkIsing_floor_mul_succ_eventually_in_expandingSquare_eq
  {c : Real} :
-- imply
  ∀ᶠ k : Nat in atTop, -(fkIsingExpandingSquareSide k : Int) ≤ ⌊c * (k + 1 : Real)⌋ ∧ ⌊c * (k + 1 : Real)⌋ < fkIsingExpandingSquareSide k := by
-- proof
  apply StatMech.Universality.fkIsing_floor_mul_succ_eventually_in_expandingSquare c

/--
[fkIsingDenseRationalPrimal_eventually_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fkIsingDenseRationalPrimal_eventually_interior_eq
  {q : Rat × Rat} :
-- imply
  ∀ᶠ k : Nat in atTop, -(fkIsingExpandingSquareSide k : Int) ≤ fkIsingDenseRationalPrimalX q k ∧ fkIsingDenseRationalPrimalX q k < fkIsingExpandingSquareSide k ∧ -(fkIsingExpandingSquareSide k : Int) ≤ fkIsingDenseRationalPrimalY q k ∧ fkIsingDenseRationalPrimalY q k < fkIsingExpandingSquareSide k := by
-- proof
  apply StatMech.Universality.fkIsingDenseRationalPrimal_eventually_interior q

/--
[fkIsingExpandingSquareScale_mul_floor_succ_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fkIsingExpandingSquareScale_mul_floor_succ_tendsto_eq
  {c : Real} :
-- imply
  Tendsto (fun k ↦ fkIsingExpandingSquareScale k * ((⌊c * (k + 1 : Real)⌋ : Int) : Real)) atTop (nhds c) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareScale_mul_floor_succ_tendsto c

/--
[fkIsingDenseRationalIncidence_embedding_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fkIsingDenseRationalIncidence_embedding_tendsto_eq
  {q : Rat × Rat} :
-- imply
  Tendsto (fun k ↦ FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k) (fkIsingSquareInteriorRadialEndpoint (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) (fkIsingDenseRationalIncidence q k))) atTop (nhds (fkIsingRationalComplex q)) := by
-- proof
  apply StatMech.Universality.fkIsingDenseRationalIncidence_embedding_tendsto q

/--
[fkIsingExpandingSquareScale_mul_natAbs_floor_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fkIsingExpandingSquareScale_mul_natAbs_floor_succ_le_eq
  {c : Real}
  {k : Nat} :
-- imply
  fkIsingExpandingSquareScale k * (⌊c * (k + 1 : Real)⌋ : Int).natAbs ≤ := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareScale_mul_natAbs_floor_succ_le c k

/--
[fkIsingDenseRationalPath_length_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean)
-/
@[path]
private lemma fkIsingDenseRationalPath_length_le_eq
  {q : Rat × Rat}
  {k : Nat} :
-- imply
  (fkIsingDenseRationalPathSteps q k : Real) * (2 * fkIsingExpandingSquareScale k) ≤ 2 * (|((q.1 : Real) + (q.2 : Real)) / 2| + |((q.1 : Real) - (q.2 : Real)) / 2| + 2) := by
-- proof
  apply StatMech.Universality.fkIsingDenseRationalPath_length_le q k


-- created on 2026-10-23
