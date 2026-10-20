import Mathlib
import sympy.Basic
import sympy.atlas.Topology.KuratowskiClosureComplement
open Set
open MathlibExt.Topology.KuratowskiClosureComplement


/--
[kuratowski_closure_complement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/KuratowskiClosureComplement.lean)
-/
@[path]
private lemma kuratowski_closure_complement_eq
  [TopologicalSpace X]
  {s : Set X} :
-- imply
  {t : Set X | Topology.ClosureCompl.IsObtainable s t}.Finite ∧
      {t : Set X | Topology.ClosureCompl.IsObtainable s t}.ncard ≤ 14 := by
-- proof
  apply MathlibExt.Topology.KuratowskiClosureComplement.kuratowski_closure_complement s


-- created on 2026-10-20
