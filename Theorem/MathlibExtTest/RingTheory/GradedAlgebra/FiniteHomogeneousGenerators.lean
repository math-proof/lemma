/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/FiniteHomogeneousGenerators.lean -/


import Lemma.Int.GradedAlgebra.FiniteHomogeneousGenerators
open MetaMathlibExt

#check @MetaMathlibExt.MultigradedPolynomialModule.exists_finset_homogeneous_generators


example (K : Type*) [Field K] (n : ℕ) (M : Type*)
    [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MetaMathlibExt.MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    ∃ s : Finset M,
      (∀ m ∈ s, ∃ α : Fin n →₀ Int, m ∈ targetGraded.component α) ∧
      Submodule.span (MvPolynomial (Fin n) K) (s : Set M) = ⊤ :=
  MetaMathlibExt.MultigradedPolynomialModule.exists_finset_homogeneous_generators K n M targetGraded

