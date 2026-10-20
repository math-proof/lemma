import Mathlib
import sympy.Basic
import sympy.atlas.Topology.Algebra.BirkhoffKakutani
open MathlibExt.Topology.Algebra.BirkhoffKakutani


/--
[birkhoff_kakutani_metrization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/BirkhoffKakutani.lean)
-/
@[path]
private lemma birkhoff_kakutani_metrization_eq
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [FirstCountableTopology G] :
-- imply
  TopologicalSpace.MetrizableSpace G := by
-- proof
  apply MathlibExt.Topology.Algebra.BirkhoffKakutani.birkhoff_kakutani_metrization


-- created on 2026-10-20
