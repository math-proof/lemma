/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedFreeResolution.lean -/


import Structure.RingTheory.GradedAlgebra.MultigradedFreeResolution


-- The identity linear map preserves each homogeneous piece.
example {K : Type*} [Field K] {n : ℕ} {M : Type*} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (g : MetaMathlibExt.MultigradedPolynomialModule K n M) :
    MetaMathlibExt.IsDegreeZero g g LinearMap.id := fun _ _ hm => hm

