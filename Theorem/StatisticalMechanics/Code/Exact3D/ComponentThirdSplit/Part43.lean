/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part45
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare_of_denominatorPositive
    {β H D : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (hDpos : 0 < D)
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))} :
    SourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare
      v β H Ω hasGhost hasOrigin hasEndpoint R
      (fun E => finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E / D)
      D := by
  refine ⟨?_, ?_⟩
  · intro E _hE
    exact
      div_nonneg
        (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
          hβ hH E)
        (le_of_lt hDpos)
  · intro E _hE
    rw [div_mul_cancel₀ _ hDpos.ne']

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_pointwiseShare
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    {atomShare :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
        ℝ}
    (h :
      SourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare
        v β H Ω hasGhost hasOrigin hasEndpoint R atomShare D) :
    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
      v β H Ω hasGhost hasOrigin hasEndpoint R
      (∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R,
        atomShare E)
      D := by
  classical
  refine ⟨?_, ?_⟩
  · exact Finset.sum_nonneg (fun E hE => h.1 E hE)
  · rw [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_sum_classifiedSet
        β H n Ω v hasGhost hasOrigin hasEndpoint R]
    calc
      (∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E)
          ≤
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω hasGhost hasOrigin hasEndpoint R,
          atomShare E * D := by
          exact Finset.sum_le_sum (fun E hE => h.2 E hE)
      _ =
        (∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω hasGhost hasOrigin hasEndpoint R,
          atomShare E) * D := by
          exact
            (Finset.sum_mul
              (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                v Ω hasGhost hasOrigin hasEndpoint R)
              atomShare D).symm

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_denominatorPositive
    {β H D : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (hDpos : 0 < D)
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))} :
    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
      v β H Ω hasGhost hasOrigin hasEndpoint R
      (∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
          D)
      D := by
  exact
    sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_pointwiseShare
      (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
      (hasGhost := hasGhost) (hasOrigin := hasOrigin)
      (hasEndpoint := hasEndpoint) (R := R)
      (atomShare := fun E =>
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
          D)
      (sourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare_of_denominatorPositive
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (R := R)
        hβ hH hDpos)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_le_pointwiseShareBudget
    {β H D budget : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    {atomShare :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
        ℝ}
    (h :
      SourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare
        v β H Ω hasGhost hasOrigin hasEndpoint R atomShare D)
    (hbudget :
      (∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R,
        atomShare E) * D ≤ budget) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R) ≤
      budget := by
  exact
    le_trans
      (sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_pointwiseShare
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (R := R)
        (atomShare := atomShare) h).2
      hbudget

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_le_normalizedClassifiedSetShare
    {β H D share : ℝ} (hDpos : 0 < D) {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    (hshare :
      (∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E / D) ≤
        share) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R) ≤
      share * D := by
  classical
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_sum_classifiedSet
      β H n Ω v hasGhost hasOrigin hasEndpoint R]
  calc
    (∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E)
        =
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R,
        (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
            D) * D := by
        exact Finset.sum_congr rfl (fun E _hE =>
          (div_mul_cancel₀
            (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
              β H E)
            hDpos.ne').symm)
    _ =
      (∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
          D) * D := by
        exact
          (Finset.sum_mul
            (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
              v Ω hasGhost hasOrigin hasEndpoint R)
            (fun E =>
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                β H E / D)
            D).symm
    _ ≤ share * D := mul_le_mul_of_nonneg_right hshare (le_of_lt hDpos)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_le_normalizedLabelShare
    {β H D share : ℝ} (hDpos : 0 < D) {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι}
    (hshare :
      (∑ i : ι,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω hasGhost hasOrigin hasEndpoint R label i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
            D) ≤
        share) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R) ≤
      share * D := by
  classical
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_label_sum
      β H n Ω v hasGhost hasOrigin hasEndpoint R label]
  calc
    (∑ i : ι,
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum
        v β H Ω hasGhost hasOrigin hasEndpoint R label i)
        =
      ∑ i : ι,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω hasGhost hasOrigin hasEndpoint R label i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E := by
        exact Finset.sum_congr rfl (fun i _hi =>
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum_eq_sum_labelSet
            v β H Ω hasGhost hasOrigin hasEndpoint R label i)
    _ =
      ∑ i : ι,
        (∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω hasGhost hasOrigin hasEndpoint R label i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
            D) * D := by
        exact Finset.sum_congr rfl (fun i _hi =>
          calc
            (∑ E ∈
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                v Ω hasGhost hasOrigin hasEndpoint R label i,
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                β H E)
                =
              ∑ E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                  v Ω hasGhost hasOrigin hasEndpoint R label i,
                (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                    β H E / D) * D := by
                exact Finset.sum_congr rfl (fun E _hE =>
                  (div_mul_cancel₀
                    (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                      β H E)
                    hDpos.ne').symm)
            _ =
              (∑ E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                  v Ω hasGhost hasOrigin hasEndpoint R label i,
                finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E / D) * D := by
                exact
                  (Finset.sum_mul
                    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                      v Ω hasGhost hasOrigin hasEndpoint R label i)
                    (fun E =>
                      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                        β H E / D)
                    D).symm)
    _ =
      (∑ i : ι,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω hasGhost hasOrigin hasEndpoint R label i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
            D) * D := by
        exact
          (Finset.sum_mul
            (Finset.univ : Finset ι)
            (fun i =>
              ∑ E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                  v Ω hasGhost hasOrigin hasEndpoint R label i,
                finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E / D)
            D).symm
    _ ≤ share * D := mul_le_mul_of_nonneg_right hshare (le_of_lt hDpos)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum_le_pointwiseShare
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    {atomShare :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
        ℝ}
    (h :
      SourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare
        v β H Ω hasGhost hasOrigin hasEndpoint R atomShare D)
    {ι : Type*} [DecidableEq ι]
    (label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι)
    (i : ι) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum
        v β H Ω hasGhost hasOrigin hasEndpoint R label i ≤
      (∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ω hasGhost hasOrigin hasEndpoint R label i,
        atomShare E) * D := by
  classical
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum_eq_sum_labelSet
      v β H Ω hasGhost hasOrigin hasEndpoint R label i]
  calc
    (∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ω hasGhost hasOrigin hasEndpoint R label i,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E)
        ≤
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ω hasGhost hasOrigin hasEndpoint R label i,
        atomShare E * D := by
        exact Finset.sum_le_sum (fun E hE =>
          h.2 E ((Finset.mem_filter.mp hE).1))
    _ =
      (∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ω hasGhost hasOrigin hasEndpoint R label i,
        atomShare E) * D := by
        exact
          (Finset.sum_mul
            (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
              v Ω hasGhost hasOrigin hasEndpoint R label i)
            atomShare D).symm

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare_of_pointwiseShare
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    {atomShare :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
        ℝ}
    (h :
      SourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare
        v β H Ω hasGhost hasOrigin hasEndpoint R atomShare D)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι} :
    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare
      v β H Ω hasGhost hasOrigin hasEndpoint R label
      (fun i =>
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω hasGhost hasOrigin hasEndpoint R label i,
          atomShare E)
      D := by
  classical
  refine ⟨?_, ?_⟩
  · intro i
    exact Finset.sum_nonneg (fun E hE =>
      h.1 E ((Finset.mem_filter.mp hE).1))
  · intro i
    exact
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum_le_pointwiseShare
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (R := R)
        (atomShare := atomShare) h label i

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare_of_denominatorPositive
    {β H D : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (hDpos : 0 < D)
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι} :
    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare
      v β H Ω hasGhost hasOrigin hasEndpoint R label
      (fun i =>
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω hasGhost hasOrigin hasEndpoint R label i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
            D)
      D := by
  exact
    sourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare_of_pointwiseShare
      (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
      (hasEndpoint := hasEndpoint) (R := R)
      (atomShare := fun E =>
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
          D)
      (sourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare_of_denominatorPositive
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (R := R)
          hβ hH hDpos)

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelDenominatorPositive
    {β H D : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (hDpos : 0 < D)
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι} :
    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
      v β H Ω hasGhost hasOrigin hasEndpoint R
      (∑ i : ι,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω hasGhost hasOrigin hasEndpoint R label i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
            D)
      D := by
  exact
    sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
      (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
      (hasGhost := hasGhost) (hasOrigin := hasOrigin)
      (hasEndpoint := hasEndpoint) (R := R)
      (label := label)
      (labelShare := fun i =>
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω hasGhost hasOrigin hasEndpoint R label i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
            D)
      (sourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare_of_denominatorPositive
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (R := R)
        (label := label) hβ hH hDpos)

end Exact3D
end StatMech
