import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
open Filter Topology StatMech StatMech.FrontierD


/--
[eventually_exists_sixVertexHalfFilledBethePerronBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean)
-/
@[path]
private lemma eventually_exists_sixVertexHalfFilledBethePerronBranch_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, ∃ p : Fin ((k + 1) + (k + 1)) → Real, SixVertexOpenRootSimplex p ∧ SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) p ∧ sixVertexSymmetricBetheEigenvalueKernel c (sixVertexEvenPositiveHalfProjection (k + 1) p) = sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by unfold sixVertexFourWidth omega) c := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexHalfFilledBethePerronBranch hc

/--
[eventually_exists_sixVertexHalfFilledPerronGaugeWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean)
-/
@[path]
private lemma eventually_exists_sixVertexHalfFilledPerronGaugeWitness_eq
  {c epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ k : Nat in atTop, ∃ p, SixVertexHalfFilledPerronGaugeWitness hc k epsilon p := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexHalfFilledPerronGaugeWitness hc hepsilon

/--
[sixVertexCanonicalPerronBetheRoots_mem_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean)
-/
@[path]
private lemma sixVertexCanonicalPerronBetheRoots_mem_open_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexOpenRootSimplex (sixVertexCanonicalPerronBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalPerronBetheRoots_mem_open hc k

/--
[sixVertexCanonicalPerronBetheRoots_is_solution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean)
-/
@[path]
private lemma sixVertexCanonicalPerronBetheRoots_is_solution_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexCanonicalPerronBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalPerronBetheRoots_is_solution hc k

/--
[eventually_sixVertexCanonicalPerronBetheRoots_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalPerronBetheRoots_witness_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, SixVertexHalfFilledPerronBranchWitness c k (sixVertexCanonicalPerronBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalPerronBetheRoots_witness hc

/--
[sixVertexCanonicalPerronPositiveHalfRoots_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean)
-/
@[path]
private lemma sixVertexCanonicalPerronPositiveHalfRoots_mem_Ioo_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalPerronPositiveHalfRoots hc k j ∈ Set.Ioo 0 Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalPerronPositiveHalfRoots_mem_Ioo hc k j

/--
[eventually_sixVertexLambdaAlongFour_eq_canonicalPerronValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean)
-/
@[path]
private lemma eventually_sixVertexLambdaAlongFour_eq_canonicalPerronValue_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexLambdaAlongFour c 0 k = sixVertexSymmetricBetheEigenvalueValue c (sixVertexCanonicalPerronPositiveHalfRoots hc k) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexLambdaAlongFour_eq_canonicalPerronValue hc

/--
[sixVertexCanonicalPerronCandidateRate_eq_rootAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean)
-/
@[path]
private lemma sixVertexCanonicalPerronCandidateRate_eq_rootAverage_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalPerronCandidateRate hc k = Real.log 2 / (sixVertexFourWidth 0 k : Real) + sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalPerronPositiveHalfRootFamily hc) k := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalPerronCandidateRate_eq_rootAverage hc k

/--
[sixVertexCentralWidthRate_eventuallyEq_canonicalPerronCandidateRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean)
-/
@[path]
private lemma sixVertexCentralWidthRate_eventuallyEq_canonicalPerronCandidateRate_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCentralWidthRate c =ᶠ[atTop] sixVertexCanonicalPerronCandidateRate hc := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralWidthRate_eventuallyEq_canonicalPerronCandidateRate hc

/--
[sixVertexCentralWidthRate_eventuallyEq_canonicalRootAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean)
-/
@[path]
private lemma sixVertexCentralWidthRate_eventuallyEq_canonicalRootAverage_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCentralWidthRate c =ᶠ[atTop] fun k => Real.log 2 / (sixVertexFourWidth 0 k : Real) + sixVertexSymmetricBetheRootAverage c (sixVertexCanonicalPerronPositiveHalfRootFamily hc) k := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralWidthRate_eventuallyEq_canonicalRootAverage hc


-- created on 2026-10-23
