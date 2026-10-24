import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.SwitchingCovariance
open Finset BigOperators Classical StatMech StatMech.Sharpness StatMech.Sharpness.RandomCurrent


/--
[switching_disconnect_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingCovariance.lean)
-/
@[path]
private lemma switching_disconnect_card_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (huv : u ≠ v) :
-- imply
  (#(m.powerset.filter (fun K => sources ends K = A)) : ℤ) - #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v})) = (if ¬ connK ends m u v then (#(m.powerset.filter (fun K => sources ends K = A)) : ℤ) else 0) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.switching_disconnect_card ends m hnd A hm huv

/--
[switching_disconnect_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingCovariance.lean)
-/
@[path]
private lemma switching_disconnect_lemma_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
  {F : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (huv : u ≠ v) :
-- imply
  (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m) - (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), F m) = ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m * (if ¬ connK ends m u v then 1 else 0) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.switching_disconnect_lemma ends m hnd A hm huv F

/--
[srcPairDisconnect_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingCovariance.lean)
-/
@[path]
private lemma srcPairDisconnect_eq_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {u v : V}
  {F : Finset ι → ℝ}
-- given
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (huv : u ≠ v) :
-- imply
  (∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m)) - (∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), F m)) = ∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m * (if ¬ connK ends m u v then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.srcPairDisconnect_eq ends hnd A huv F


-- created on 2026-10-23
