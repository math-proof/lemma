import Mathlib
import sympy.Basic
import Theorem.Topology.Algebra.BirkhoffKakutani
open MathlibExt.Topology.Algebra.BirkhoffKakutani


namespace MathlibExt.Topology.Algebra.BirkhoffKakutani

/--
[birkhoff_kakutani_metrization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/BirkhoffKakutani.lean)
-/
@[path]
lemma birkhoff_kakutani_metrization
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [FirstCountableTopology G] :
-- imply
  TopologicalSpace.MetrizableSpace G := by
-- proof
  have hU : Filter.IsCountablyGenerated
    (@uniformity G (IsTopologicalGroup.leftUniformSpace G)) := by
    change Filter.IsCountablyGenerated
      (Filter.comap (fun p : G × G => p.1⁻¹ * p.2) (nhds 1))
    infer_instance
  have hT0 : T0Space G := inferInstance
  exact @UniformSpace.metrizableSpace _ (IsTopologicalGroup.leftUniformSpace G) hU hT0

end MathlibExt.Topology.Algebra.BirkhoffKakutani


-- created on 2026-10-20
-- updated on 2026-10-23
