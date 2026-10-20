import Mathlib
import sympy.Basic
import sympy.atlas.Topology.Algebra.Group.OpenProfiniteCompletion
open CategoryTheory
open scoped Pointwise
open ProfiniteGrp.OpenProfiniteCompletion


/--
[etaFn_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean)
-/
@[path]
private lemma etaFn_apply_eq
  {G : Type u} [Group G] [TopologicalSpace G]
  {x : G}
  {H : Index G} :
-- imply
  ((etaFn G x).val H : G ⧸ H.1.toSubgroup) =
    QuotientGroup.mk x := by
-- proof
  apply ProfiniteGrp.OpenProfiniteCompletion.etaFn_apply G x H

/--
[etaFn_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean)
-/
@[path]
private lemma etaFn_continuous_eq
  {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] :
-- imply
  Continuous (etaFn G) := by
-- proof
  apply ProfiniteGrp.OpenProfiniteCompletion.etaFn_continuous G

/--
[denseRange_etaFn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean)
-/
@[path]
private lemma denseRange_etaFn_eq
  {G : Type u} [Group G] [TopologicalSpace G] :
-- imply
  DenseRange (etaFn G) := by
-- proof
  apply ProfiniteGrp.OpenProfiniteCompletion.denseRange_etaFn G

/--
[denseRange_eta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean)
-/
@[path]
private lemma denseRange_eta_eq
  {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] :
-- imply
  DenseRange (eta G) := by
-- proof
  apply ProfiniteGrp.OpenProfiniteCompletion.denseRange_eta G


-- created on 2026-10-20
