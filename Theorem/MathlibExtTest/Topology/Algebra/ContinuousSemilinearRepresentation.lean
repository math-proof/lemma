/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/Algebra/ContinuousSemilinearRepresentation.lean -/


import Class.Topology.Algebra.ContinuousSemilinearRepresentation
import Mathlib.Algebra.Module.PUnit
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Int


-- The class can be constructed directly from its two substantive laws.
example (G R M : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M]
    [MulSemiringAction G R] [DistribMulAction G M]
    [ContinuousSMul G R] [ContinuousSMul G M] [ContinuousSMul R M]
    (h : ∀ (g : G) (r : R) (x : M), g • (r • x) = (g • r) • (g • x))
    (h_top : IsHomeomorph (Module.Free.chooseBasis R M).equivFun) :
    IsContinuousSemilinearRepresentation G R M where
  smul_distrib_smul := h
  isHomeomorph_equivFun := h_top

-- The inherited semilinearity law is available as an instance.
example (G R M : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M]
    [MulSemiringAction G R] [DistribMulAction G M]
    [ContinuousSMul G R] [ContinuousSMul G M] [ContinuousSMul R M]
    [IsContinuousSemilinearRepresentation G R M]
    (g : G) (r : R) (x : M) : g • (r • x) = (g • r) • (g • x) :=
  smul_distrib_smul g r x

-- The transported-topology condition is recoverable from the class.
example (G R M : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M]
    [MulSemiringAction G R] [DistribMulAction G M]
    [ContinuousSMul G R] [ContinuousSMul G M] [ContinuousSMul R M]
    [IsContinuousSemilinearRepresentation G R M] :
    IsHomeomorph (Module.Free.chooseBasis R M).equivFun :=
  IsContinuousSemilinearRepresentation.isHomeomorph_equivFun G

