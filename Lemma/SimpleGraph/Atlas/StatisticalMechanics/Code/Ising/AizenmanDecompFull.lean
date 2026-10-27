import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.AizenmanDecompFull.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Ising StatMech.Ising.AizenmanDecomp


/--
[aid_conn_trans_xy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_conn_trans_xy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hoy : connK ends m o y)
  (hox : connK ends m o x) :
-- imply
  connK ends m x y := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_conn_trans_xy ends m hoy hox

/--
[aid_conn_trans_ox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_conn_trans_ox_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hxy : connK ends m x y)
  (hoy : connK ends m o y) :
-- imply
  connK ends m o x := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_conn_trans_ox ends m hxy hoy

/--
[aid_conn_trans_oy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_conn_trans_oy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hxy : connK ends m x y)
  (hox : connK ends m o x) :
-- imply
  connK ends m o y := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_conn_trans_oy ends m hxy hox

/--
[aid_noneConn_not_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_noneConn_not_allConn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (h : aid_noneConn ends m o x y) :
-- imply
  ¬ aid_allConn ends m o x y := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_noneConn_not_allConn ends m h

/--
[aid_backbone_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_backbone_trichotomy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  asd_ghsBackboneFactor ends m o x y = 1 ∨ asd_ghsBackboneFactor ends m o x y = 0 ∨ asd_ghsBackboneFactor ends m o x y = -2 := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_backbone_trichotomy ends m o x y

/--
[aid_backbone_value_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_backbone_value_none_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (h : aid_noneConn ends m o x y) :
-- imply
  asd_ghsBackboneFactor ends m o x y = 1 := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_backbone_value_none ends m h

/--
[aid_backbone_value_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_backbone_value_all_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (h : aid_allConn ends m o x y) :
-- imply
  asd_ghsBackboneFactor ends m o x y = -2 := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_backbone_value_all ends m h

/--
[aid_backbone_value_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_backbone_value_one_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hnotall : ¬ aid_allConn ends m o x y)
  (hnotnone : ¬ aid_noneConn ends m o x y) :
-- imply
  asd_ghsBackboneFactor ends m o x y = 0 := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_backbone_value_one ends m hnotall hnotnone

/--
[aid_backbone_factor_nonneg_not_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_backbone_factor_nonneg_not_all_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hnotall : ¬ aid_allConn ends m o x y) :
-- imply
  0 ≤ asd_ghsBackboneFactor ends m o x y := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_backbone_factor_nonneg_not_all ends m hnotall

/--
[aid_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_mass_nonneg_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {φ : Finset ι → ℝ}
  {S : Finset V}
-- given
  (hφnn : ∀ K, 0 ≤ φ K) :
-- imply
  0 ≤ aid_mass ends m φ S := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_mass_nonneg ends m φ hφnn S

/--
[aid_gap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_gap_eq_eq
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
  (hm : Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  aid_gap ends m φ A o x y = aid_mass ends m φ A * asd_ghsBackboneFactor ends m o x y := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_gap_eq ends m hnd A hm hox hoy hxy φ hφ

/--
[aid_per_super_nonneg_not_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_per_super_nonneg_not_all_eq
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
  (hm : Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hnotall : ¬ aid_allConn ends m o x y) :
-- imply
  0 ≤ aid_gap ends m φ A o x y := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_per_super_nonneg_not_all ends m hnd A hm hox hoy hxy φ hφnn hφ hnotall

/--
[aid_gap_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_gap_allConn_eq
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
  (hm : Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aid_allConn ends m o x y) :
-- imply
  aid_gap ends m φ A o x y = -2 * aid_mass ends m φ A := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_gap_allConn ends m hnd A hm hox hoy hxy φ hφ hall

/--
[aid_gap_noneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_gap_noneConn_eq
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
  (hm : Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hnone : aid_noneConn ends m o x y) :
-- imply
  aid_gap ends m φ A o x y = aid_mass ends m φ A := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_gap_noneConn ends m hnd A hm hox hoy hxy φ hφ hnone

/--
[aid_gap_exactlyOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_gap_exactlyOne_eq
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
  (hm : Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hnotall : ¬ aid_allConn ends m o x y)
  (hnotnone : ¬ aid_noneConn ends m o x y) :
-- imply
  aid_gap ends m φ A o x y = 0 := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_gap_exactlyOne ends m hnd A hm hox hoy hxy φ hφ hnotall hnotnone

/--
[aid_inclusion_exclusion_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_inclusion_exclusion_split_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ} :
-- imply
  ∑ m ∈ M, aid_gap ends m (Φ m) A o x y = (∑ m ∈ M, aid_mass ends m (Φ m) A) - (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {x, y})) - (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {o, y})) - (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {o, x})) := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_inclusion_exclusion_split ends M A o x y Φ

/--
[aid_decomp_allConn_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_decomp_allConn_sum_eq
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
  (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
-- imply
  ∑ m ∈ M.filter (fun m => aid_allConn ends m o x y), aid_gap ends m (Φ m) A o x y = -2 * ∑ m ∈ M.filter (fun m => aid_allConn ends m o x y), aid_mass ends m (Φ m) A := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_decomp_allConn_sum ends M hnd A hm hox hoy hxy Φ hΦ

/--
[aid_decomp_notAllConn_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_decomp_notAllConn_sum_eq
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
  (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
-- imply
  ∑ m ∈ M.filter (fun m => ¬ aid_allConn ends m o x y), aid_gap ends m (Φ m) A o x y = ∑ m ∈ M.filter (fun m => aid_noneConn ends m o x y), aid_mass ends m (Φ m) A := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_decomp_notAllConn_sum ends M hnd A hm hox hoy hxy Φ hΦ

/--
[aid_inclusion_exclusion_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_inclusion_exclusion_decomp_eq
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
  (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
-- imply
  ∑ m ∈ M, aid_gap ends m (Φ m) A o x y = (∑ m ∈ M.filter (fun m => aid_noneConn ends m o x y), aid_mass ends m (Φ m) A) - 2 * (∑ m ∈ M.filter (fun m => aid_allConn ends m o x y), aid_mass ends m (Φ m) A) := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_inclusion_exclusion_decomp ends M hnd A hm hox hoy hxy Φ hΦ

/--
[aid_inclusion_exclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_inclusion_exclusion_eq
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
  (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
  (hdom : 2 * (∑ m ∈ M.filter (fun m => aid_allConn ends m o x y), aid_mass ends m (Φ m) A) ≤ ∑ m ∈ M.filter (fun m => aid_noneConn ends m o x y), aid_mass ends m (Φ m) A) :
-- imply
  0 ≤ ∑ m ∈ M, aid_gap ends m (Φ m) A o x y := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_inclusion_exclusion ends M hnd A hm hox hoy hxy Φ hΦ hdom

/--
[aid_ghs_distinct_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanDecompFull.lean)
-/
@[path]
private lemma aid_ghs_distinct_site_eq
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
  (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
  (hdom : 2 * (∑ m ∈ M.filter (fun m => aid_allConn ends m o x y), aid_mass ends m (Φ m) A) ≤ ∑ m ∈ M.filter (fun m => aid_noneConn ends m o x y), aid_mass ends m (Φ m) A) :
-- imply
  (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {x, y})) + (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {o, y})) + (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {o, x})) ≤ ∑ m ∈ M, aid_mass ends m (Φ m) A := by
-- proof
  apply StatMech.Ising.AizenmanDecomp.aid_ghs_distinct_site ends M hnd A hm hox hoy hxy Φ hΦ hdom


-- created on 2026-10-23
