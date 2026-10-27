import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.GroupTheory.BurnsidePaqb.ClassSum.Part3
open BurnsidePaqb
open Classical


namespace Definitions
end Definitions
namespace BurnsidePaqb

/--
[conjClass_eq_of_isConj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean)
-/
@[path]
private lemma conjClass_eq_of_isConj
  [Group G] [Fintype G]
  {g1 g2 : G}
-- given
  (h : IsConj g1 g2) :
-- imply
  conjClass g1 = conjClass g2 := by
-- proof
  ext x
  rw [mem_conjClass_iff, mem_conjClass_iff]
  exact ⟨fun hx => hx.trans h, fun hx => hx.trans (isConj_comm.mp h)⟩

end BurnsidePaqb

/--
[classSum_central](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean)
-/
@[path]
private lemma classSum_central_eq
  [Group G] [Fintype G]
  {g h : G} :
-- imply
  classSum (conjClass g) * MonoidAlgebra.of ℂ G h =
    MonoidAlgebra.of ℂ G h * classSum (conjClass g) := by
-- proof
  apply BurnsidePaqb.classSum_central g h

/--
[classSum_central'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean)
-/
@[path]
private lemma classSum_central'_eq
  [Group G] [Fintype G]
  {g : G}
  {w : MonoidAlgebra ℂ G} :
-- imply
  w * classSum (conjClass g) = classSum (conjClass g) * w := by
-- proof
  apply BurnsidePaqb.classSum_central' g w

/--
[classRep_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean)
-/
@[path]
private lemma classRep_spec_eq
  [Group G] [Fintype G]
  {l : ConjClasses G} :
-- imply
  ConjClasses.mk (classRep l) = l := by
-- proof
  apply BurnsidePaqb.classRep_spec l

/--
[carrier_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean)
-/
@[path]
private lemma carrier_toFinset_eq
  [Group G] [Fintype G]
  {l : ConjClasses G} :
-- imply
  (ConjClasses.carrier l).toFinset = conjClass (classRep l) := by
-- proof
  classical
  apply BurnsidePaqb.carrier_toFinset l

/--
[structConst_conj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean)
-/
@[path]
private lemma structConst_conj_eq
  [Group G] [Fintype G]
  {gi gj u z : G}
-- given
  (h : IsConj u z) :
-- imply
  structConst (conjClass gi) (conjClass gj) u =
    structConst (conjClass gi) (conjClass gj) z := by
-- proof
  apply BurnsidePaqb.structConst_conj gi gj u z h

/--
[coeff_classSum_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean)
-/
@[path]
private lemma coeff_classSum_mul_eq
  [Group G] [Fintype G]
  {Ci Cj : Finset G}
  {u : G} :
-- imply
  (classSum Ci * classSum Cj).coeff u = (structConst Ci Cj u : ℂ) := by
-- proof
  apply BurnsidePaqb.coeff_classSum_mul Ci Cj u

/--
[classSum_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean)
-/
@[path]
private lemma classSum_mul_eq
  [Group G] [Fintype G]
  {gi gj : G} :
-- imply
  classSum (conjClass gi) * classSum (conjClass gj)
    = ∑ l : ConjClasses G, (structConst (conjClass gi) (conjClass gj) (classRep l) : ℂ)
    • classSum (ConjClasses.carrier l).toFinset := by
-- proof
  classical
  apply BurnsidePaqb.classSum_mul gi gj

/--
[classSum_carrier_central](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean)
-/
@[path]
private lemma classSum_carrier_central_eq
  [Group G] [Fintype G]
  {l : ConjClasses G}
  {w : MonoidAlgebra ℂ G} :
-- imply
  w * classSum (ConjClasses.carrier l).toFinset
    = classSum (ConjClasses.carrier l).toFinset * w := by
-- proof
  classical
  apply BurnsidePaqb.classSum_carrier_central l w


-- created on 2026-10-24
