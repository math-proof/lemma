import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall
open Finset StatMech StatMech.FrontierD


/--
[finiteUpperCumulative_of_bidegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean)
-/
@[path]
private lemma finiteUpperCumulative_of_bidegree_eq
  [Fintype Source]
  [Fintype Target]
  {sourceGrade : Source → Nat}
  {targetGrade : Target → Nat}
  {degree : Nat}
-- given
  (related : Source → Target → Prop)
  (hdegree : 0 < degree)
  (hforward : ∀ source, degree ≤ (Finset.univ.filter (related source)).card)
  (hinverse : ∀ target, (Finset.univ.filter fun source => related source target).card ≤ degree)
  (hmonotone : ∀ source target, related source target → sourceGrade source ≤ targetGrade target) :
-- imply
  ∀ grade, (Finset.univ.filter fun source => grade ≤ sourceGrade source).card ≤ (Finset.univ.filter fun target => grade ≤ targetGrade target).card := by
-- proof
  apply StatMech.FrontierD.finiteUpperCumulative_of_bidegree related sourceGrade targetGrade degree hdegree hforward hinverse hmonotone

/--
[finiteUpperCumulative_of_twoBranchCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean)
-/
@[path]
private lemma finiteUpperCumulative_of_twoBranchCapacity_eq
  [Fintype Source]
  [Fintype Target]
  {sourceGrade : Source → Nat}
  {targetGrade : Target → Nat}
-- given
  (related : Source → Target → Prop)
  (hforward : ∀ source, 2 ≤ (Finset.univ.filter (related source)).card)
  (hinverse : ∀ target, (Finset.univ.filter fun source => related source target).card ≤ 2)
  (hmonotone : ∀ source target, related source target → sourceGrade source ≤ targetGrade target) :
-- imply
  ∀ grade, (Finset.univ.filter fun source => grade ≤ sourceGrade source).card ≤ (Finset.univ.filter fun target => grade ≤ targetGrade target).card := by
-- proof
  apply StatMech.FrontierD.finiteUpperCumulative_of_twoBranchCapacity related sourceGrade targetGrade hforward hinverse hmonotone

/--
[exists_injective_gradeMonotone_of_twoBranchCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean)
-/
@[path]
private lemma exists_injective_gradeMonotone_of_twoBranchCapacity_eq
  [Fintype Source]
  [Fintype Target]
  {sourceGrade : Source → Nat}
  {targetGrade : Target → Nat}
-- given
  (related : Source → Target → Prop)
  (hforward : ∀ source, 2 ≤ (Finset.univ.filter (related source)).card)
  (hinverse : ∀ target, (Finset.univ.filter fun source => related source target).card ≤ 2)
  (hmonotone : ∀ source target, related source target → sourceGrade source ≤ targetGrade target) :
-- imply
  ∃ matching : Source → Target, Function.Injective matching ∧ ∀ source, sourceGrade source ≤ targetGrade (matching source) := by
-- proof
  apply StatMech.FrontierD.exists_injective_gradeMonotone_of_twoBranchCapacity related sourceGrade targetGrade hforward hinverse hmonotone

/--
[TwoBranchMonotoneEmbeddings.forward_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean)
-/
@[path]
private lemma forward_degree_eq
  [Fintype Target]
  {sourceGrade : Source → Nat}
  {targetGrade : Target → Nat}
  {embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade targetGrade}
  {source : Source} :
-- imply
  2 ≤ (Finset.univ.filter (embeddings.Related source)).card := by
-- proof
  apply StatMech.FrontierD.TwoBranchMonotoneEmbeddings.forward_degree embeddings source

/--
[TwoBranchMonotoneEmbeddings.branch_inverseChoice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean)
-/
@[path]
private lemma branch_inverseChoice_eq
  {sourceGrade : Source → Nat}
  {targetGrade : Target → Nat}
  {embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade targetGrade}
  {target : Target}
  {source : {source : Source // embeddings.Related source target}} :
-- imply
  embeddings.branch (embeddings.inverseChoice target source) source.1 = target := by
-- proof
  apply StatMech.FrontierD.TwoBranchMonotoneEmbeddings.branch_inverseChoice embeddings target source

/--
[TwoBranchMonotoneEmbeddings.inverse_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean)
-/
@[path]
private lemma inverse_degree_eq
  [Fintype Source]
  {sourceGrade : Source → Nat}
  {targetGrade : Target → Nat}
  {embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade targetGrade}
  {target : Target} :
-- imply
  (Finset.univ.filter fun source => embeddings.Related source target).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.TwoBranchMonotoneEmbeddings.inverse_degree embeddings target

/--
[TwoBranchMonotoneEmbeddings.upperCumulative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean)
-/
@[path]
private lemma upperCumulative_eq
  [Fintype Source]
  [Fintype Target]
  {sourceGrade : Source → Nat}
  {targetGrade : Target → Nat}
  {embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade targetGrade} :
-- imply
  ∀ grade, (Finset.univ.filter fun source => grade ≤ sourceGrade source).card ≤ (Finset.univ.filter fun target => grade ≤ targetGrade target).card := by
-- proof
  apply StatMech.FrontierD.TwoBranchMonotoneEmbeddings.upperCumulative embeddings

/--
[TwoBranchMonotoneEmbeddings.exists_injective_gradeMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean)
-/
@[path]
private lemma exists_injective_gradeMonotone_eq
  [Fintype Source]
  [Fintype Target]
  {sourceGrade : Source → Nat}
  {targetGrade : Target → Nat}
  {embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade targetGrade} :
-- imply
  ∃ matching : Source → Target, Function.Injective matching ∧ ∀ source, sourceGrade source ≤ targetGrade (matching source) := by
-- proof
  apply StatMech.FrontierD.TwoBranchMonotoneEmbeddings.exists_injective_gradeMonotone embeddings


-- created on 2026-10-23
