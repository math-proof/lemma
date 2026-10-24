import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
open Finset BigOperators SimpleGraph StatMech StatMech.Sharpness StatMech.Sharpness.GhostCurrentRep


/--
[gcr_pairCount_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_pairCount_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {A : Finset V} :
-- imply
  (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)) = (if RandomCurrent.sources (endsM G m) univ = A then (1 : ℝ) else 0) * (#((univ : Finset (Copy G m)).powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ) := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_pairCount_empty G m A

/--
[gcr_pairCount_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_pairCount_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {A : Finset V}
  {u v : V} :
-- imply
  (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A ∆ {u, v} then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = ({u, v} : Finset V) then 1 else 0)) = (if RandomCurrent.sources (endsM G m) univ = A then (1 : ℝ) else 0) * (#((univ : Finset (Copy G m)).powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v})) : ℝ) := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_pairCount_pair G m A u v

/--
[gcr_pairCount_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_pairCount_disconn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {A : Finset V}
  {u v : V} :
-- imply
  (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0)) = (if RandomCurrent.sources (endsM G m) univ = A then (1 : ℝ) else 0) * (if ¬ RandomCurrent.connK (endsM G m) univ u v then (1 : ℝ) else 0) * (#((univ : Finset (Copy G m)).powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ) := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_pairCount_disconn G m A u v

/--
[gcr_superposition_switching_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_superposition_switching_gap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {A : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)) - (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A ∆ {u, v} then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = ({u, v} : Finset V) then 1 else 0)) = ∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0) := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_superposition_switching_gap G m A huv

/--
[gcr_summable_edgecopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_summable_edgecopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V} :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0)) * weight G β J (ofEdgeFun G m)) := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_summable_edgecopy G β J A B

/--
[gcr_summable_edgecopy_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_summable_edgecopy_disconn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (hJnn : ∀ e, 0 ≤ J e)
  (hβ : 0 ≤ β) :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0)) * weight G β J (ofEdgeFun G m)) := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_summable_edgecopy_disconn G β J hJnn hβ A u v

/--
[gcr_sourcePairSum_switching_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_sourcePairSum_switching_gap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  sourcePairSum G β J A ∅ - sourcePairSum G β J (A ∆ {u, v}) {u, v} = sourcePairDisconnSum G β J A ∅ u v := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_sourcePairSum_switching_gap G β J A huv

/--
[gcr_currentSum_ghostRep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_currentSum_ghostRep_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v) :
-- imply
  currentSum G β J A * currentSum G β J ∅ - currentSum G β J (A ∆ {u, v}) * currentSum G β J {u, v} = sourcePairDisconnSum G β J A ∅ u v := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_currentSum_ghostRep G β J A huv

/--
[gcr_ghostCurrentRep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_ghostCurrentRep_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
  {Z mom₃ mom₁ mom₂ : ℝ}
-- given
  (huv : u ≠ v)
  (hZ : Z = currentSum G β J ∅)
  (hZne : Z ≠ 0)
  (hrep₃ : mom₃ = currentSum G β J A / Z)
  (hrep₁ : mom₁ = currentSum G β J (A ∆ {u, v}) / Z)
  (hrep₂ : mom₂ = currentSum G β J {u, v} / Z) :
-- imply
  Z ^ 2 * (mom₃ - mom₁ * mom₂) = sourcePairDisconnSum G β J A ∅ u v := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_ghostCurrentRep G β J A huv Z mom₃ mom₁ mom₂ hZ hZne hrep₃ hrep₁ hrep₂

/--
[gcr_sourcePairSum_switching_gap_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_sourcePairSum_switching_gap_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  sourcePairSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) ({0, 1, 2} : Finset (Fin 3)) ∅ - sourcePairSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) (({0, 1, 2} : Finset (Fin 3)) ∆ {0, 2}) {0, 2} = sourcePairDisconnSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) ({0, 1, 2} : Finset (Fin 3)) ∅ 0 2 := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_sourcePairSum_switching_gap_nonvacuous G

/--
[gcr_currentSum_ghostRep_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GhostCurrentRep.lean)
-/
@[path]
private lemma gcr_currentSum_ghostRep_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  currentSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) ({0, 1, 2} : Finset (Fin 3)) * currentSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) ∅ - currentSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) (({0, 1, 2} : Finset (Fin 3)) ∆ {0, 2}) * currentSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) {0, 2} = sourcePairDisconnSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) ({0, 1, 2} : Finset (Fin 3)) ∅ 0 2 := by
-- proof
  apply StatMech.Sharpness.GhostCurrentRep.gcr_currentSum_ghostRep_nonvacuous G


-- created on 2026-10-23
