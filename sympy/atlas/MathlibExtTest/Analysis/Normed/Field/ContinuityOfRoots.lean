/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Normed/Field/ContinuityOfRoots.lean -/


import Lemma.Polynomial.Normed.Field.ContinuityOfRoots
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace


namespace Polynomial

open IsDedekindDomain

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

example (f : K[X]) (hf : f.Monic) (hirr : Irreducible f)
    (hsep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
      l1Norm (NormedField.toAbsoluteValue K) (f - g) < δ →
      ∀ β : AlgebraicClosure K, aeval β g = 0 →
        ∃ α : AlgebraicClosure K, aeval α f = 0 ∧
          AlgebraicClosure.IsClosestConjugate K α β ∧
          IntermediateField.adjoin K {α} =
            IntermediateField.adjoin K {β} :=
  exists_isClosestConjugate_root_of_l1Norm_sub_lt K f hf hirr hsep

example (f : K[X]) (hf : f.Monic) (hirr : Irreducible f)
    (hsep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
      l1Norm (NormedField.toAbsoluteValue K) (f - g) < δ →
      Irreducible g ∧ g.Separable :=
  exists_pos_irreducible_and_separable_of_l1Norm_sub_lt K f hf hirr hsep

example (a : K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
      l1Norm (NormedField.toAbsoluteValue K) (X - C a - g) < δ →
      ∀ β : AlgebraicClosure K, aeval β g = 0 →
        ∃ α : AlgebraicClosure K, aeval α (X - C a) = 0 ∧
          AlgebraicClosure.IsClosestConjugate K α β ∧
          IntermediateField.adjoin K {α} =
            IntermediateField.adjoin K {β} :=
  exists_isClosestConjugate_root_of_l1Norm_sub_lt _ _ (monic_X_sub_C a)
    (irreducible_X_sub_C a) (separable_X_sub_C)

example (f : K[X]) (hf : f.Monic) (hirr : Irreducible f)
    (hsep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
      l1Norm (NormedField.toAbsoluteValue K) (f - g) < δ →
      ∀ β : AlgebraicClosure K, aeval β g = 0 →
        ∃ α : AlgebraicClosure K, aeval α f = 0 ∧
          AlgebraicClosure.IsClosestConjugate K α β ∧
          IntermediateField.adjoin K {α} ≤
            IntermediateField.adjoin K {β} ∧
          IntermediateField.adjoin K {β} ≤
            IntermediateField.adjoin K {α} := by
  obtain ⟨δ, hδpos, hmain⟩ :=
    exists_isClosestConjugate_root_of_l1Norm_sub_lt K f hf hirr hsep
  refine ⟨δ, hδpos, fun g hg hclose β hβ => ?_⟩
  obtain ⟨α, hαroot, hcloseAB, heq⟩ := hmain g hg hclose β hβ
  exact ⟨α, hαroot, hcloseAB, le_of_eq heq, le_of_eq heq.symm⟩

example {K L : Type*} [Field K] [NontriviallyNormedField L]
    [IsUltrametricDist L] [CompleteSpace L] [Algebra K L]
    (hdense : DenseRange (algebraMap K L))
    (f : L[X]) (hf : f.Monic) (hirr : Irreducible f) (hsep : f.Separable)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : K[X], g.Monic ∧ g.natDegree = f.natDegree ∧
      l1Norm (NormedField.toAbsoluteValue L)
        (f - g.map (algebraMap K L)) < ε ∧
      Irreducible (g.map (algebraMap K L)) ∧
      (g.map (algebraMap K L)).Separable := by
  obtain ⟨g, hg, hdeg, hclose, hmapirr, hmapsep⟩ :=
    exists_monic_and_natDegree_eq_and_l1Norm_sub_lt_and_map_irreducible_and_separable
      hdense f hf hirr hsep hε
  exact ⟨g, hg, hdeg, hclose, hmapirr, hmapsep⟩

open scoped Valued in
example {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (f : (HeightOneSpectrum.adicCompletion K v)[X])
    (hf : f.Monic) (hirr : Irreducible f) (hsep : f.Separable)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : K[X], g.Monic ∧ g.natDegree = f.natDegree ∧
      l1Norm (NormedField.toAbsoluteValue (HeightOneSpectrum.adicCompletion K v))
        (f - g.map (algebraMap K (HeightOneSpectrum.adicCompletion K v))) < ε ∧
      Irreducible (g.map (algebraMap K (HeightOneSpectrum.adicCompletion K v))) ∧
      (g.map (algebraMap K (HeightOneSpectrum.adicCompletion K v))).Separable :=
  exists_monic_and_natDegree_eq_and_l1Norm_sub_lt_and_map_irreducible_and_separable
    (K := K) (L := HeightOneSpectrum.adicCompletion K v)
    (HeightOneSpectrum.denseRange_algebraMap K v) f hf hirr hsep hε

end Polynomial
