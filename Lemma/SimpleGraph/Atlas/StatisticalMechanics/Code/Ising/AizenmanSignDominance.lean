import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Ising StatMech.Sharpness StatMech.Sharpness.RandomCurrent


/--
[asd_weight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_weight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n : Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ Sharpness.weight G β J n := by
-- proof
  apply StatMech.Ising.asd_weight_nonneg G β J hβ hJ n

/--
[asd_splitWeightedSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_splitWeightedSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {F : ℝ}
  {A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hF : 0 ≤ F) :
-- imply
  0 ≤ splitWeightedSum G β J m F A := by
-- proof
  apply StatMech.Ising.asd_splitWeightedSum_nonneg G β J hβ hJ m F hF A

/--
[asd_switching_weighted_edgecopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_switching_weighted_edgecopy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P : Finset ι}
  {A : Finset V}
  {φ : Finset ι → ℝ}
-- given
  (hP : P ⊆ m)
  (hφ : ∀ K, K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ sources ends P), φ K = ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_switching_weighted_edgecopy ends m P hP A φ hφ

/--
[asd_switching_weighted_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_switching_weighted_indicator_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (huv : u ≠ v)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), φ K = (if connK ends m u v then 1 else 0) * ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_switching_weighted_indicator ends m hnd A hm huv φ hφ

/--
[asd_signDominance_edgecopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_signDominance_edgecopy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (huv : u ≠ v)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), φ K ≤ ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_signDominance_edgecopy ends m hnd A hm huv φ hφnn hφ

/--
[asd_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_signDominance_eq
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
  apply StatMech.Sharpness.RandomCurrent.asd_signDominance ends m hnd A hm huv w hwnn hw

/--
[asd_signedSplit_nonneg_edgecopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_signedSplit_nonneg_edgecopy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (huv : u ≠ v)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  0 ≤ (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) - ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), φ K := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_signedSplit_nonneg_edgecopy ends m hnd A hm huv φ hφnn hφ

/--
[asd_ghsSigned_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_ghsSigned_eq_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {x, y}), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, y}), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, x}), φ K) = (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) * (1 - (if connK ends m x y then 1 else 0) - (if connK ends m o y then 1 else 0) - (if connK ends m o x then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_ghsSigned_eq ends m hnd A hm hox hoy hxy φ hφ

/--
[asd_ghsBackboneFactor_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_ghsBackboneFactor_allConn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hxy : connK ends m x y)
  (hoy : connK ends m o y)
  (hox : connK ends m o x) :
-- imply
  asd_ghsBackboneFactor ends m o x y = -2 := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_ghsBackboneFactor_allConn ends m hxy hoy hox

/--
[asd_ghsBackboneFactor_noConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_ghsBackboneFactor_noConn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hxy : ¬ connK ends m x y)
  (hoy : ¬ connK ends m o y)
  (hox : ¬ connK ends m o x) :
-- imply
  asd_ghsBackboneFactor ends m o x y = 1 := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_ghsBackboneFactor_noConn ends m hxy hoy hox

/--
[asd_ghsBackboneFactor_not_signDefinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_ghsBackboneFactor_not_signDefinite_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m₁ m₂ : Finset ι}
  {o x y : V}
-- given
  (h₁ : connK ends m₁ x y ∧ connK ends m₁ o y ∧ connK ends m₁ o x)
  (h₂ : ¬ connK ends m₂ x y ∧ ¬ connK ends m₂ o y ∧ ¬ connK ends m₂ o x) :
-- imply
  asd_ghsBackboneFactor ends m₁ o x y < 0 ∧ 0 < asd_ghsBackboneFactor ends m₂ o x y := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_ghsBackboneFactor_not_signDefinite ends m₁ m₂ h₁ h₂

/--
[asd_ghsBackboneFactor_nonneg_singleBackbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_ghsBackboneFactor_nonneg_singleBackbone_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (h : ¬ (connK ends m x y ∧ connK ends m o y) ∧ ¬ (connK ends m x y ∧ connK ends m o x) ∧ ¬ (connK ends m o y ∧ connK ends m o x)) :
-- imply
  0 ≤ asd_ghsBackboneFactor ends m o x y := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_ghsBackboneFactor_nonneg_singleBackbone ends m h

/--
[asd_ghsSigned_nonneg_singleBackbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_ghsSigned_nonneg_singleBackbone_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hsingle : ¬ (connK ends m x y ∧ connK ends m o y) ∧ ¬ (connK ends m x y ∧ connK ends m o x) ∧ ¬ (connK ends m o y ∧ connK ends m o x)) :
-- imply
  0 ≤ (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {x, y}), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, y}), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, x}), φ K) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_ghsSigned_nonneg_singleBackbone ends m hnd A hm hox hoy hxy φ hφnn hφ hsingle

/--
[asd_switching_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_switching_weighted_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P Q : Finset ι}
  {A : Finset V}
  {φ : Finset ι → ℝ}
-- given
  (hP : P ⊆ m)
  (hQ : Q ⊆ m)
  (hφ : ∀ K, K ⊆ m → φ ((K ∆ P) ∆ Q) = φ K) :
-- imply
  ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ sources ends P ∆ sources ends Q), φ K = ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_switching_weighted ends m P Q hP hQ A φ hφ

/--
[asd_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_signDominance_eq_2
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v s t : V}
  {φ : Finset ι → ℝ}
-- given
  (huv : u ≠ v)
  (hst : s ≠ t)
  (hconnuv : connK ends m u v)
  (hconnst : connK ends m s t)
  (hφ : ∀ K P Q, P ⊆ m → Q ⊆ m → K ⊆ m → φ ((K ∆ P) ∆ Q) = φ K) :
-- imply
  ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}), φ K = ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.asd_signDominance ends m A huv hst hconnuv hconnst φ hφ

/--
[asd_signCancel_native](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_signCancel_native_eq
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
  apply StatMech.Ising.asd_signCancel_native G β J m huv hconn F A

/--
[asd_signDominance_native](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_signDominance_native_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {F : ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hF : 0 ≤ F)
  (hm : Sharpness.sources G m = A)
  (huv : u ≠ v)
  (hconn_odd_or_disc : connP (oddEdges G.edgeFinset m) u v ∨ ¬ connP (posEdges G.edgeFinset m) u v) :
-- imply
  splitWeightedSum G β J m F (A ∆ {u, v}) ≤ splitWeightedSum G β J m F A := by
-- proof
  apply StatMech.Ising.asd_signDominance_native G β J hβ hJ m hnd F hF A hm huv hconn_odd_or_disc

/--
[asd_signDominance_derived](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean)
-/
@[path]
private lemma asd_signDominance_derived_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {F : ℝ}
  {u v : V}
-- given
  (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (huv : u ≠ v)
  (hsrc : Sharpness.sources G m = {u, v}) :
-- imply
  splitWeightedSum G β J m F {u, v} = splitWeightedSum G β J m F ∅ := by
-- proof
  apply StatMech.Ising.asd_signDominance_derived G β J m hnd F huv hsrc


-- created on 2026-10-23
