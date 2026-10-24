import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[analyticAt_real_arctan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma analyticAt_real_arctan_eq
  {x : Real} :
-- imply
  AnalyticAt Real Real.arctan x := by
-- proof
  apply StatMech.FrontierD.analyticAt_real_arctan x

/--
[analyticAt_sixVertexTheta_joint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma analyticAt_sixVertexTheta_joint_eq
  {q : Real × (Real × Real)}
-- given
  (hc : 2 < q.1) :
-- imply
  AnalyticAt Real (fun z : Real × (Real × Real) => sixVertexTheta z.1 z.2.1 z.2.2) q := by
-- proof
  apply StatMech.FrontierD.analyticAt_sixVertexTheta_joint q hc

/--
[analyticAt_sixVertexBetheResidual_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma analyticAt_sixVertexBetheResidual_family_eq
  {N n : Nat}
  {q : Real × (Fin n → Real)}
-- given
  (hc : 2 < q.1) :
-- imply
  AnalyticAt Real (fun z : Real × (Fin n → Real) => fun j => sixVertexBetheResidual z.1 N n z.2 j) q := by
-- proof
  apply StatMech.FrontierD.analyticAt_sixVertexBetheResidual_family N n q hc

/--
[analyticAt_sixVertexBetheResidualGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma analyticAt_sixVertexBetheResidualGraph_eq
  {N n : Nat}
  {q : Real × (Fin n → Real)}
-- given
  (hc : 2 < q.1) :
-- imply
  AnalyticAt Real (sixVertexBetheResidualGraph N n) q := by
-- proof
  apply StatMech.FrontierD.analyticAt_sixVertexBetheResidualGraph N n q hc

/--
[sixVertexBetheResidualGraph_fderiv_injective_of_rootJacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma sixVertexBetheResidualGraph_fderiv_injective_of_rootJacobian_eq
  {N n : Nat}
  {c : Real}
  {p : Fin n → Real}
-- given
  (hc : 2 < c)
  (hjac : Function.Injective (sixVertexBetheRootJacobian N n c p)) :
-- imply
  Function.Injective (fderiv Real (sixVertexBetheResidualGraph N n) (c, p)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheResidualGraph_fderiv_injective_of_rootJacobian hc hjac

/--
[isOpen_sixVertexStrictRootTuples](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma isOpen_sixVertexStrictRootTuples_eq
  {n : Nat} :
-- imply
  IsOpen {p : Fin n → Real | StrictMono p} := by
-- proof
  apply StatMech.FrontierD.isOpen_sixVertexStrictRootTuples n

/--
[isOpen_sixVertexRootsInOpenInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma isOpen_sixVertexRootsInOpenInterval_eq
  {n : Nat} :
-- imply
  IsOpen {p : Fin n → Real | SixVertexRootsInOpenInterval p} := by
-- proof
  apply StatMech.FrontierD.isOpen_sixVertexRootsInOpenInterval n

/--
[isOpen_sixVertexNonsymmetricOpenRootDomain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma isOpen_sixVertexNonsymmetricOpenRootDomain_eq
  {n : Nat} :
-- imply
  IsOpen {p : Fin n → Real | StrictMono p ∧ SixVertexRootsInOpenInterval p} := by
-- proof
  apply StatMech.FrontierD.isOpen_sixVertexNonsymmetricOpenRootDomain n

/--
[isCompact_sixVertexBetheFixedPointSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma isCompact_sixVertexBetheFixedPointSet_eq
  {c : Real}
  {N n : Nat}
-- given
  (hc : 2 < c) :
-- imply
  IsCompact (sixVertexBetheFixedPointSet c N n) := by
-- proof
  apply StatMech.FrontierD.isCompact_sixVertexBetheFixedPointSet hc N n

/--
[sixVertexBetheFixedPointSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma sixVertexBetheFixedPointSet_nonempty_eq
  {c : Real}
  {N n : Nat}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N) :
-- imply
  (sixVertexBetheFixedPointSet c N n).Nonempty := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheFixedPointSet_nonempty hc hN hhalf

/--
[sixVertexBetheFixedPointSet_subset_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma sixVertexBetheFixedPointSet_subset_open_eq
  {c : Real}
  {N n : Nat}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n ≤ N) :
-- imply
  sixVertexBetheFixedPointSet c N n ⊆ {p | SixVertexOpenRootSimplex p} := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheFixedPointSet_subset_open hc hhalf

/--
[sixVertexBetheFixedPointSet_eq_solutionSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma sixVertexBetheFixedPointSet_eq_solutionSet_eq
  {c : Real}
  {N n : Nat}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexBetheFixedPointSet c N n = {p | SixVertexClosedRootSimplex p ∧ SixVertexSatisfiesBetheEquations c N n p} := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheFixedPointSet_eq_solutionSet hN

/--
[continuous_sixVertexBetheResidual_family_clamp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma continuous_sixVertexBetheResidual_family_clamp_eq
  {a : Real}
  {N n : Nat}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (fun q : Real × (Fin n → Real) => fun j => sixVertexBetheResidual (max a q.1) N n q.2 j) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBetheResidual_family_clamp ha N n

/--
[continuous_sixVertexBetheUpdate_family_clamp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma continuous_sixVertexBetheUpdate_family_clamp_eq
  {a : Real}
  {N n : Nat}
-- given
  (ha : 2 < a)
  (hN : 0 < N) :
-- imply
  Continuous (fun q : Real × (Fin n → Real) => sixVertexBetheUpdate (max a q.1) N n q.2) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBetheUpdate_family_clamp ha hN

/--
[isCompact_sixVertexBetheContinuationSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma isCompact_sixVertexBetheContinuationSet_eq
  {a b : Real}
  {N n : Nat}
-- given
  (ha : 2 < a)
  (hN : 0 < N) :
-- imply
  IsCompact (sixVertexBetheContinuationSet a b N n) := by
-- proof
  apply StatMech.FrontierD.isCompact_sixVertexBetheContinuationSet ha hN

/--
[sixVertexBetheContinuationSet_fiber_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma sixVertexBetheContinuationSet_fiber_nonempty_eq
  {a b t : Real}
  {N n : Nat}
-- given
  (ha : 2 < a)
  (ht : t ∈ Set.Icc a b)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N) :
-- imply
  ∃ p, (t, p) ∈ sixVertexBetheContinuationSet a b N n := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheContinuationSet_fiber_nonempty ha ht hN hhalf

/--
[sixVertexBetheContinuationSet_fst_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma sixVertexBetheContinuationSet_fst_image_eq
  {a b : Real}
  {N n : Nat}
-- given
  (ha : 2 < a)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N) :
-- imply
  Prod.fst '' sixVertexBetheContinuationSet a b N n = Set.Icc a b := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheContinuationSet_fst_image ha hN hhalf

/--
[sixVertexBetheContinuationSet_subset_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma sixVertexBetheContinuationSet_subset_open_eq
  {a b : Real}
  {N n : Nat}
-- given
  (ha : 2 < a)
  (hhalf : 2 * n ≤ N) :
-- imply
  sixVertexBetheContinuationSet a b N n ⊆ {q | SixVertexOpenRootSimplex q.2} := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheContinuationSet_subset_open ha hhalf

/--
[continuous_sixVertexBetheContinuationProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma continuous_sixVertexBetheContinuationProjection_eq
  {a b : Real}
  {N n : Nat} :
-- imply
  Continuous (@sixVertexBetheContinuationProjection a b N n) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBetheContinuationProjection

/--
[exists_sixVertexContinuousBetheBranch_of_isLocalHomeomorph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma exists_sixVertexContinuousBetheBranch_of_isLocalHomeomorph_eq
  {a b c₀ : Real}
  {N n : Nat}
  {z₀ : SixVertexBetheContinuationSpace a b N n}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hlocal : IsLocalHomeomorph (@sixVertexBetheContinuationProjection a b N n))
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin n → Real), roots c₀ = z₀.1.2 ∧ ∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N n (roots t) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousBetheBranch_of_isLocalHomeomorph ha hab hc₀ hN hlocal z₀ hz₀

/--
[exists_sixVertexLocalAnalyticBetheBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma exists_sixVertexLocalAnalyticBetheBranch_eq
  {N n : Nat}
  {c : Real}
  {p : Fin n → Real}
-- given
  (hc : 2 < c)
  (hsol : SixVertexSatisfiesBetheEquations c N n p)
  (hjac : Function.Injective (fderiv Real (sixVertexBetheResidualGraph N n) (c, p))) :
-- imply
  Nonempty (SixVertexLocalAnalyticBetheBranch N n c p) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexLocalAnalyticBetheBranch hc hsol hjac

/--
[exists_sixVertexLocalAnalyticBetheBranch_of_rootJacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma exists_sixVertexLocalAnalyticBetheBranch_of_rootJacobian_eq
  {N n : Nat}
  {c : Real}
  {p : Fin n → Real}
-- given
  (hc : 2 < c)
  (hsol : SixVertexSatisfiesBetheEquations c N n p)
  (hjac : Function.Injective (sixVertexBetheRootJacobian N n c p)) :
-- imply
  Nonempty (SixVertexLocalAnalyticBetheBranch N n c p) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexLocalAnalyticBetheBranch_of_rootJacobian hc hsol hjac

/--
[isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_rootJacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_rootJacobian_eq
  {a b : Real}
  {N n : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N n)}
-- given
  (ha : 2 < a)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N)
  (hjac : ∀ q ∈ C, Function.Injective (sixVertexBetheRootJacobian N n q.1.1 q.1.2)) :
-- imply
  IsLocalHomeomorphOn (@sixVertexBetheContinuationProjection a b N n) C := by
-- proof
  apply StatMech.FrontierD.isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_rootJacobian ha hN hhalf C hjac

/--
[isLocalHomeomorph_sixVertexBetheContinuationProjection_of_rootJacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma isLocalHomeomorph_sixVertexBetheContinuationProjection_of_rootJacobian_eq
  {a b : Real}
  {N n : Nat}
-- given
  (ha : 2 < a)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N)
  (hjac : ∀ q ∈ sixVertexBetheContinuationSet a b N n, Function.Injective (sixVertexBetheRootJacobian N n q.1 q.2)) :
-- imply
  IsLocalHomeomorph (@sixVertexBetheContinuationProjection a b N n) := by
-- proof
  apply StatMech.FrontierD.isLocalHomeomorph_sixVertexBetheContinuationProjection_of_rootJacobian ha hN hhalf hjac

/--
[continuous_sixVertexBetheContinuationProjectionOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma continuous_sixVertexBetheContinuationProjectionOn_eq
  {a b : Real}
  {N n : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N n)} :
-- imply
  Continuous (sixVertexBetheContinuationProjectionOn C) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBetheContinuationProjectionOn C

/--
[isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_rootJacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_rootJacobian_eq
  {a b : Real}
  {N n : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N n)}
-- given
  (ha : 2 < a)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N)
  (hC : IsOpen C)
  (hjac : ∀ q ∈ C, Function.Injective (sixVertexBetheRootJacobian N n q.1.1 q.1.2)) :
-- imply
  IsLocalHomeomorph (sixVertexBetheContinuationProjectionOn C) := by
-- proof
  apply StatMech.FrontierD.isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_rootJacobian ha hN hhalf C hC hjac

/--
[exists_sixVertexContinuousBetheBranch_of_compactComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma exists_sixVertexContinuousBetheBranch_of_compactComponent_eq
  {a b c₀ : Real}
  {N n : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N n)}
  {z₀ : C}
-- given
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hcompact : IsCompact C)
  (hlocal : IsLocalHomeomorph (sixVertexBetheContinuationProjectionOn C))
  (hz₀ : sixVertexBetheContinuationProjectionOn C z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin n → Real), roots c₀ = z₀.1.1.2 ∧ ∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N n (roots t) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousBetheBranch_of_compactComponent hab hc₀ hN C hcompact hlocal z₀ hz₀

/--
[exists_sixVertexContinuousBetheBranch_of_regularComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma exists_sixVertexContinuousBetheBranch_of_regularComponent_eq
  {a b c₀ : Real}
  {N n : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N n)}
  {z₀ : C}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N)
  (hCopen : IsOpen C)
  (hCcompact : IsCompact C)
  (hjac : ∀ q ∈ C, Function.Injective (sixVertexBetheRootJacobian N n q.1.1 q.1.2))
  (hz₀ : sixVertexBetheContinuationProjectionOn C z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin n → Real), roots c₀ = z₀.1.1.2 ∧ ∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N n (roots t) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousBetheBranch_of_regularComponent ha hab hc₀ hN hhalf C hCopen hCcompact hjac z₀ hz₀

/--
[exists_sixVertexContinuousBetheBranch_of_rootJacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean)
-/
@[path]
private lemma exists_sixVertexContinuousBetheBranch_of_rootJacobian_eq
  {a b c₀ : Real}
  {N n : Nat}
  {z₀ : SixVertexBetheContinuationSpace a b N n}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N)
  (hjac : ∀ q ∈ sixVertexBetheContinuationSet a b N n, Function.Injective (sixVertexBetheRootJacobian N n q.1 q.2))
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin n → Real), roots c₀ = z₀.1.2 ∧ ∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N n (roots t) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousBetheBranch_of_rootJacobian ha hab hc₀ hN hhalf hjac z₀ hz₀


-- created on 2026-10-23
