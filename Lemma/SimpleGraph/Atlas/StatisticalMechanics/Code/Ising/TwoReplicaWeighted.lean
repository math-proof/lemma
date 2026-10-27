import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
open Finset Classical StatMech StatMech.Ising


/--
[weight_reflect_split_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplicaWeighted.lean)
-/
@[path]
private lemma weight_reflect_split_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {K : Current V}
-- given
  (hK : ∀ e, K e ≤ m e) :
-- imply
  Sharpness.weight G β J (reflect m P K) * Sharpness.weight G β J (fun e => m e - reflect m P K e) = Sharpness.weight G β J K * Sharpness.weight G β J (fun e => m e - K e) := by
-- proof
  apply StatMech.Ising.weight_reflect_split_eq G β J m P hK

/--
[ising_switching_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplicaWeighted.lean)
-/
@[path]
private lemma ising_switching_weighted_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {u v : V}
  {F : ℝ}
  {A : Finset V}
-- given
  (huv : u ≠ v)
  (hconn : connP (oddEdges G.edgeFinset m) u v) :
-- imply
  splitWeightedSum G β J m F (A ∆ {u, v}) = splitWeightedSum G β J m F A := by
-- proof
  apply StatMech.Ising.ising_switching_weighted G β J m huv hconn F A

/--
[ising_switching_weighted_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplicaWeighted.lean)
-/
@[path]
private lemma ising_switching_weighted_vanishing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {A : Finset V}
  {u v : V}
  {F : ℝ}
-- given
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : Sharpness.sources G m = A)
  (huv : u ≠ v)
  (hconn : ¬ connP (posEdges G.edgeFinset m) u v) :
-- imply
  splitWeightedSum G β J m F (A ∆ {u, v}) = 0 := by
-- proof
  apply StatMech.Ising.ising_switching_weighted_vanishing G β J m hnd A hm huv hconn F

/--
[ising_switching_weighted_sourceless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplicaWeighted.lean)
-/
@[path]
private lemma ising_switching_weighted_sourceless_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {u v : V}
  {F : ℝ}
-- given
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (huv : u ≠ v)
  (hsrc : Sharpness.sources G m = {u, v}) :
-- imply
  splitWeightedSum G β J m F {u, v} = splitWeightedSum G β J m F ∅ := by
-- proof
  apply StatMech.Ising.ising_switching_weighted_sourceless G β J m hnd huv hsrc F

/--
[ising_two_point_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplicaWeighted.lean)
-/
@[path]
private lemma ising_two_point_switching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {F : ℝ}
  {A : Finset V} :
-- imply
  splitWeightedSum G β J m F A = F * Sharpness.weight G β J m * ∑ K : {K : Current V // ∀ e, K e ≤ m e}, (if Sharpness.sources G K.1 = A then (∏ e ∈ G.edgeFinset, (Nat.choose (m e) (K.1 e) : ℝ)) else 0) := by
-- proof
  apply StatMech.Ising.ising_two_point_switching G β J m F A


-- created on 2026-10-23
