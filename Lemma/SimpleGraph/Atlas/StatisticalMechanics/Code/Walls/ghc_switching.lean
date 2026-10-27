import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.ghc_switching
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[ghc_switching_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_switching.lean)
-/
@[path]
private lemma ghc_switching_signDominance_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
  {w : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (huv : u ≠ v)
  (hwnn : ∀ K, 0 ≤ w K)
  (hw : ∀ K P, P ⊆ m → K ⊆ m → w (K ∆ P) = w K) :
-- imply
  ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), w K ≤ ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), w K := by
-- proof
  apply StatMech.Walls.ghc_switching_signDominance ends m hnd A hm huv w hwnn hw

/--
[ghc_switching_signedSplit_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_switching.lean)
-/
@[path]
private lemma ghc_switching_signedSplit_nonneg_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
  {w : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (huv : u ≠ v)
  (hwnn : ∀ K, 0 ≤ w K)
  (hw : ∀ K P, P ⊆ m → K ⊆ m → w (K ∆ P) = w K) :
-- imply
  0 ≤ (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), w K) - ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), w K := by
-- proof
  apply StatMech.Walls.ghc_switching_signedSplit_nonneg ends m hnd A hm huv w hwnn hw

/--
[ghc_switching_signDominance_native](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_switching.lean)
-/
@[path]
private lemma ghc_switching_signDominance_native_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 W → ℝ}
  {m : StatMech.Ising.Current W}
  {F : ℝ}
  {A : Finset W}
  {u v : W}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hF : 0 ≤ F)
  (hm : StatMech.Sharpness.sources G m = A)
  (huv : u ≠ v)
  (hconn_odd_or_disc : StatMech.Ising.connP (StatMech.Ising.oddEdges G.edgeFinset m) u v ∨ ¬ StatMech.Ising.connP (StatMech.Ising.posEdges G.edgeFinset m) u v) :
-- imply
  StatMech.Ising.splitWeightedSum G β J m F (A ∆ {u, v}) ≤ StatMech.Ising.splitWeightedSum G β J m F A := by
-- proof
  apply StatMech.Walls.ghc_switching_signDominance_native G β J hβ hJ m hnd F hF A hm huv hconn_odd_or_disc

/--
[ghc_switching_signCancel_native](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_switching.lean)
-/
@[path]
private lemma ghc_switching_signCancel_native_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 W → ℝ}
  {m : StatMech.Ising.Current W}
  {u v : W}
  {F : ℝ}
  {A : Finset W}
-- given
  (huv : u ≠ v)
  (hconn : StatMech.Ising.connP (StatMech.Ising.oddEdges G.edgeFinset m) u v) :
-- imply
  StatMech.Ising.splitWeightedSum G β J m F (A ∆ {u, v}) = StatMech.Ising.splitWeightedSum G β J m F A := by
-- proof
  apply StatMech.Walls.ghc_switching_signCancel_native G β J m huv hconn F A

/--
[ghc_switching_signedSplit_nonneg_native](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_switching.lean)
-/
@[path]
private lemma ghc_switching_signedSplit_nonneg_native_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 W → ℝ}
  {m : StatMech.Ising.Current W}
  {F : ℝ}
  {A : Finset W}
  {u v : W}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hF : 0 ≤ F)
  (hm : StatMech.Sharpness.sources G m = A)
  (huv : u ≠ v)
  (hconn_odd_or_disc : StatMech.Ising.connP (StatMech.Ising.oddEdges G.edgeFinset m) u v ∨ ¬ StatMech.Ising.connP (StatMech.Ising.posEdges G.edgeFinset m) u v) :
-- imply
  0 ≤ StatMech.Ising.splitWeightedSum G β J m F A - StatMech.Ising.splitWeightedSum G β J m F (A ∆ {u, v}) := by
-- proof
  apply StatMech.Walls.ghc_switching_signedSplit_nonneg_native G β J hβ hJ m hnd F hF A hm huv hconn_odd_or_disc


-- created on 2026-10-23
