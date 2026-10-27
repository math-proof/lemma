import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.AizenmanHdom.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Sharpness StatMech.Sharpness.RandomCurrent


/--
[ahd_backbone_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_backbone_exists_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hall : aie_allConn ends m o x y)
  (hox : o ≠ x)
  (hxy : x ≠ y) :
-- imply
  (∃ P ⊆ m, sources ends P = {o, x}) ∧ (∃ Q ⊆ m, sources ends Q = {x, y}) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_backbone_exists ends m hall hox hxy

/--
[ahd_mass_reroute_xy_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_mass_reroute_xy_eq_eq
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
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_mass ends m φ (A ∆ {x, y}) = aie_mass ends m φ A := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_mass_reroute_xy_eq ends m hnd A hm hxy φ hφ hall

/--
[ahd_mass_reroute_oy_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_mass_reroute_oy_eq_eq
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
  (hoy : o ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_mass ends m φ (A ∆ {o, y}) = aie_mass ends m φ A := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_mass_reroute_oy_eq ends m hnd A hm hoy φ hφ hall

/--
[ahd_mass_reroute_ox_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_mass_reroute_ox_eq_eq
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
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_mass ends m φ (A ∆ {o, x}) = aie_mass ends m φ A := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_mass_reroute_ox_eq ends m hnd A hm hox φ hφ hall

/--
[ahd_mass_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_mass_reroute_eq
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
  (hox : o ≠ x)
  (hxy : x ≠ y)
  (hφ2 : ∀ K P Q, P ⊆ m → Q ⊆ m → K ⊆ m → φ ((K ∆ P) ∆ Q) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_mass ends m φ (A ∆ {o, x} ∆ {x, y}) = aie_mass ends m φ A := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_mass_reroute ends m A hox hxy φ hφ2 hall

/--
[ahd_gap_eq_neg_two_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_gap_eq_neg_two_mass_eq
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
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_gap_eq_neg_two_mass ends m hnd A hm hox hoy hxy φ hφ hall

/--
[ahd_per_super_allConn_gap_nonneg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_per_super_allConn_gap_nonneg_iff_eq
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
  (hall : aie_allConn ends m o x y) :
-- imply
  0 ≤ aie_gap ends m φ A o x y ↔ aie_mass ends m φ A = 0 := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_per_super_allConn_gap_nonneg_iff ends m hnd A hm hox hoy hxy φ hφnn hφ hall

/--
[ahd_closure_iff_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_closure_iff_hdom_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : ∀ m ∈ M, sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
-- imply
  (0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y) ↔ (2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_closure_iff_hdom ends M hnd A hm hox hoy hxy Φ hΦ

/--
[ahd_triEnds_nd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_triEnds_nd_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  ∀ i ∈ ({0, 1, 2} : Finset (Fin 3)), ¬ (ahd_triEnds i).IsDiag := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_triEnds_nd

/--
[ahd_tri_conn_ox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_tri_conn_ox_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  connK ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 1 := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_tri_conn_ox

/--
[ahd_tri_conn_xy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_tri_conn_xy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  connK ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 1 2 := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_tri_conn_xy

/--
[ahd_tri_conn_oy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_tri_conn_oy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  connK ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 2 := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_tri_conn_oy

/--
[ahd_tri_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_tri_allConn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  aie_allConn ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 1 2 := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_tri_allConn

/--
[ahd_tri_mass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_tri_mass_pos_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  (0 : ℝ) < aie_mass ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) (fun _ => 1) (sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_tri_mass_pos

/--
[ahd_hdom_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_hdom_refutable_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  ¬ (2 * (∑ m ∈ ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter (fun m => aie_allConn ahd_triEnds m 0 1 2), aie_mass ahd_triEnds m (fun _ => 1) (sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3)))) ≤ ∑ m ∈ ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter (fun m => aie_noneConn ahd_triEnds m 0 1 2), aie_mass ahd_triEnds m (fun _ => 1) (sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3)))) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_hdom_refutable

/--
[ahd_closure_of_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_closure_of_hdom_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : ∀ m ∈ M, sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
  (hdom : 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) :
-- imply
  0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_closure_of_hdom ends M hnd A hm hox hoy hxy Φ hΦ hdom

/--
[ahd_ghs_distinct_site_of_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanHdom.lean)
-/
@[path]
private lemma ahd_ghs_distinct_site_of_hdom_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : ∀ m ∈ M, sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
  (hdom : 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) :
-- imply
  (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {x, y})) + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, y})) + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, x})) ≤ ∑ m ∈ M, aie_mass ends m (Φ m) A := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.ahd_ghs_distinct_site_of_hdom ends M hnd A hm hox hoy hxy Φ hΦ hdom


-- created on 2026-10-23
