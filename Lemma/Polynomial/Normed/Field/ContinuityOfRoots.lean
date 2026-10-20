import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Normed.Field.ContinuityOfRoots
open Polynomial


/--
[exists_isClosestConjugate_root_of_l1Norm_sub_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Field/ContinuityOfRoots.lean)
-/
@[path]
private lemma exists_isClosestConjugate_root_of_l1Norm_sub_lt_eq
  [Ring K] [NontriviallyNormedField K'] [IsUltrametricDist K'] [CompleteSpace K'] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {v : AbsoluteValue K ℝ}
  {f : K[X]}
-- given
  (hf : f.Monic)
  (hirr : Irreducible f)
  (hsep : f.Separable) :
-- imply
  ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
    l1Norm (NormedField.toAbsoluteValue K) (f - g) < δ →
    ∀ β : AlgebraicClosure K, aeval β g = 0 →
    ∃ α : AlgebraicClosure K, aeval α f = 0 ∧
    AlgebraicClosure.IsClosestConjugate K α β ∧
    IntermediateField.adjoin K {α} = IntermediateField.adjoin K {β} := by
-- proof
  apply Polynomial.exists_isClosestConjugate_root_of_l1Norm_sub_lt v K f hf hirr hsep

/--
[exists_pos_irreducible_and_separable_of_l1Norm_sub_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Field/ContinuityOfRoots.lean)
-/
@[path]
private lemma exists_pos_irreducible_and_separable_of_l1Norm_sub_lt_eq
  [Ring K] [NontriviallyNormedField K'] [IsUltrametricDist K'] [CompleteSpace K'] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {v : AbsoluteValue K ℝ}
  {f : K[X]}
-- given
  (hf : f.Monic)
  (hirr : Irreducible f)
  (hsep : f.Separable) :
-- imply
  ∃ δ : ℝ, 0 < δ ∧ ∀ g : K[X], g.Monic →
    l1Norm (NormedField.toAbsoluteValue K) (f - g) < δ →
    Irreducible g ∧ g.Separable := by
-- proof
  apply Polynomial.exists_pos_irreducible_and_separable_of_l1Norm_sub_lt v K f hf hirr hsep

/--
[exists_monic_and_natDegree_eq_and_l1Norm_sub_lt_and_map_irreducible_and_separable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Field/ContinuityOfRoots.lean)
-/
@[path]
private lemma exists_monic_and_natDegree_eq_and_l1Norm_sub_lt_and_map_irreducible_and_separable_eq
  [Ring K] [NontriviallyNormedField K'] [IsUltrametricDist K'] [CompleteSpace K'] [Field K] [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] [Algebra K L]
  {v : AbsoluteValue K ℝ}
  {f : L[X]}
  {ε : ℝ}
-- given
  (hdense : DenseRange (algebraMap K L))
  (hf : f.Monic)
  (hirr : Irreducible f)
  (hsep : f.Separable)
  (hε : 0 < ε) :
-- imply
  ∃ g : K[X], g.Monic ∧ g.natDegree = f.natDegree ∧
    l1Norm (NormedField.toAbsoluteValue L)
    (f - g.map (algebraMap K L)) < ε ∧
    Irreducible (g.map (algebraMap K L)) ∧
    (g.map (algebraMap K L)).Separable := by
-- proof
  apply Polynomial.exists_monic_and_natDegree_eq_and_l1Norm_sub_lt_and_map_irreducible_and_separable v hdense f hf hirr hsep hε


-- created on 2026-10-20
