import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyDischarge
open Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.FluxEdgeCopy


/--
[edgecopy_disconnect_count_eq_switching_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyDischarge.lean)
-/
@[path]
private lemma edgecopy_disconnect_count_eq_switching_gap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {A : Finset V}
  {u v : V}
-- given
  (hnd : ∀ i ∈ (univ : Finset (Copy G m)), ¬ (endsM G m i).IsDiag)
  (hA : RandomCurrent.sources (endsM G m) univ = A)
  (huv : u ≠ v) :
-- imply
  (∑ S : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0)) = ((#((univ : Finset (Copy G m)).powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ) - #((univ : Finset (Copy G m)).powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v}))) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.edgecopy_disconnect_count_eq_switching_gap G m A u v hnd hA huv

/--
[sourcePairDisconnSum_eq_switching_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyDischarge.lean)
-/
@[path]
private lemma sourcePairDisconnSum_eq_switching_gap_eq
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
  sourcePairDisconnSum G β J A ∅ u v = ∑' m : ↥G.edgeFinset → ℕ, (if RandomCurrent.sources (endsM G m) univ = A then ((#((univ : Finset (Copy G m)).powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ) - #((univ : Finset (Copy G m)).powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v}))) else 0) * weight G β J (ofEdgeFun G m) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sourcePairDisconnSum_eq_switching_gap G β J A u v huv

/--
[sourcePairDisconnSum_eq_switching_gap_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyDischarge.lean)
-/
@[path]
private lemma sourcePairDisconnSum_eq_switching_gap_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  sourcePairDisconnSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) ({0, 1, 2} : Finset (Fin 3)) ∅ 0 2 = ∑' m : ↥(⊤ : SimpleGraph (Fin 3)).edgeFinset → ℕ, (if RandomCurrent.sources (endsM (⊤ : SimpleGraph (Fin 3)) m) univ = ({0, 1, 2} : Finset (Fin 3)) then ((#((univ : Finset (Copy (⊤ : SimpleGraph (Fin 3)) m)).powerset.filter (fun K => RandomCurrent.sources (endsM (⊤ : SimpleGraph (Fin 3)) m) K = ({0, 1, 2} : Finset (Fin 3)))) : ℝ) - #((univ : Finset (Copy (⊤ : SimpleGraph (Fin 3)) m)).powerset.filter (fun K => RandomCurrent.sources (endsM (⊤ : SimpleGraph (Fin 3)) m) K = ({0, 1, 2} : Finset (Fin 3)) ∆ {0, 2}))) else 0) * weight (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) (ofEdgeFun (⊤ : SimpleGraph (Fin 3)) m) := by
-- proof
  apply StatMech.Sharpness.FluxEdgeCopy.sourcePairDisconnSum_eq_switching_gap_nonvacuous G


-- created on 2026-10-23
