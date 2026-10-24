import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc4_scalesum
open Finset MeasureTheory StatMech StatMech.Walls


/--
[oc4_codingProb_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean)
-/
@[path]
private lemma oc4_codingProb_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : α → ℕ → ConfigSpace E → ℝ}
  {x : α}
  {j : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  oc4_codingProb μ (σ : Fin n → E) g x j = Lindeberg.mean μ (g x j) := by
-- proof
  apply StatMech.Walls.oc4_codingProb_eq_mean μ hpos hμ1 σ g x j

/--
[oc4_codingProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean)
-/
@[path]
private lemma oc4_codingProb_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {g : α → ℕ → ConfigSpace E → ℝ}
  {x : α}
  {j : ℕ}
-- given
  (hg : ∀ x j ω, 0 ≤ g x j ω) :
-- imply
  0 ≤ oc4_codingProb μ σ g x j := by
-- proof
  apply StatMech.Walls.oc4_codingProb_nonneg μ σ g hg x j

/--
[oc4_codingProb_nonneg_of_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean)
-/
@[path]
private lemma oc4_codingProb_nonneg_of_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : α → ℕ → ConfigSpace E → ℝ}
  {x : α}
  {j : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hg : ∀ x j ω, 0 ≤ g x j ω) :
-- imply
  0 ≤ oc4_codingProb μ (σ : Fin n → E) g x j := by
-- proof
  apply StatMech.Walls.oc4_codingProb_nonneg_of_mean μ hpos hμ1 σ g hg x j

/--
[oc4_codingScaleSum_le_fourD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean)
-/
@[path]
private lemma oc4_codingScaleSum_le_fourD_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {g : α → ℕ → ConfigSpace E → ℝ}
  {Λ : Finset α}
  {ru rv : ℕ}
  {u v : α}
  {qu qv : ℕ → ℝ}
-- given
  (hg : ∀ x j ω, 0 ≤ g x j ω)
  (hne : Λ.Nonempty)
  (hru : ru ≤ n)
  (hrv : rv ≤ n)
  (hu : u ∈ Λ)
  (hv : v ∈ Λ)
  (hcompu : ∀ k, qu k ≤ oc4_codingProb μ σ g u ((k : ℤ) - (ru : ℤ)).natAbs)
  (hcompv : ∀ k, qv k ≤ oc4_codingProb μ σ g v ((k : ℤ) - (rv : ℤ)).natAbs) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, (qu k + qv k) ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), oc4_codingProb μ σ g x j) := by
-- proof
  apply StatMech.Walls.oc4_codingScaleSum_le_fourD μ σ g hg Λ hne ru rv hru hrv u v hu hv qu qv hcompu hcompv

/--
[oc4_box_crossing_scale_sum_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean)
-/
@[path]
private lemma oc4_box_crossing_scale_sum_codingFrame_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {g : α → ℕ → ConfigSpace E → ℝ}
  {Λ : Finset α}
  {ru rv : ℕ}
  {u v : α}
  {qu qv : ℕ → ℝ}
-- given
  (hg : ∀ x j ω, 0 ≤ g x j ω)
  (hne : Λ.Nonempty)
  (hru : ru ≤ n)
  (hrv : rv ≤ n)
  (hu : u ∈ Λ)
  (hv : v ∈ Λ)
  (hcompu : ∀ k, qu k ≤ ∫ uu, g u ((k : ℤ) - (ru : ℤ)).natAbs (codeMap μ σ uu) ∂(Vcube n))
  (hcompv : ∀ k, qv k ≤ ∫ uu, g v ((k : ℤ) - (rv : ℤ)).natAbs (codeMap μ σ uu) ∂(Vcube n)) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, (qu k + qv k) ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), ∫ uu, g x j (codeMap μ σ uu) ∂(Vcube n)) := by
-- proof
  apply StatMech.Walls.oc4_box_crossing_scale_sum_codingFrame μ σ g hg Λ hne ru rv hru hrv u v hu hv qu qv hcompu hcompv

/--
[oc4_box_crossing_scale_sum_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean)
-/
@[path]
private lemma oc4_box_crossing_scale_sum_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : α → ℕ → ConfigSpace E → ℝ}
  {Λ : Finset α}
  {ru rv : ℕ}
  {u v : α}
  {qu qv : ℕ → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hg : ∀ x j ω, 0 ≤ g x j ω)
  (hne : Λ.Nonempty)
  (hru : ru ≤ n)
  (hrv : rv ≤ n)
  (hu : u ∈ Λ)
  (hv : v ∈ Λ)
  (hcompu : ∀ k, qu k ≤ Lindeberg.mean μ (g u ((k : ℤ) - (ru : ℤ)).natAbs))
  (hcompv : ∀ k, qv k ≤ Lindeberg.mean μ (g v ((k : ℤ) - (rv : ℤ)).natAbs)) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, (qu k + qv k) ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), Lindeberg.mean μ (g x j)) := by
-- proof
  apply StatMech.Walls.oc4_box_crossing_scale_sum_mean μ hpos hμ1 σ g hg Λ hne ru rv hru hrv u v hu hv qu qv hcompu hcompv

/--
[oc4_eq_revealment_family_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean)
-/
@[path]
private lemma oc4_eq_revealment_family_sum_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {g : α → ℕ → ConfigSpace E → ℝ}
  {Λ : Finset α}
  {ru rv : ℕ}
  {u v : α}
  {qu qv : ℕ → ℝ}
-- given
  (hg : ∀ x j ω, 0 ≤ g x j ω)
  (hne : Λ.Nonempty)
  (hru : ru ≤ n)
  (hrv : rv ≤ n)
  (hu : u ∈ Λ)
  (hv : v ∈ Λ)
  (hcompu : ∀ k, qu k ≤ oc4_codingProb μ σ g u ((k : ℤ) - (ru : ℤ)).natAbs)
  (hcompv : ∀ k, qv k ≤ oc4_codingProb μ σ g v ((k : ℤ) - (rv : ℤ)).natAbs) :
-- imply
  oc4_codingScaleSum_le_fourD μ σ g hg Λ hne ru rv hru hrv u v hu hv qu qv hcompu hcompv = revealment_family_sum_le Λ hne (fun x j => oc4_codingProb μ σ g x j) (fun x j => oc4_codingProb_nonneg μ σ g hg x j) n ru rv hru hrv u v hu hv qu qv hcompu hcompv := by
-- proof
  apply StatMech.Walls.oc4_eq_revealment_family_sum_le μ σ g hg Λ hne ru rv hru hrv u v hu hv qu qv hcompu hcompv

/--
[oc4_scale_sum_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean)
-/
@[path]
private lemma oc4_scale_sum_nonvacuous_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {Λ : Finset α}
  {ru rv : ℕ}
  {u v : α}
-- given
  (hne : Λ.Nonempty)
  (hru : ru ≤ n)
  (hrv : rv ≤ n)
  (hu : u ∈ Λ)
  (hv : v ∈ Λ) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, ((fun _ => (0 : ℝ)) k + (fun _ => (0 : ℝ)) k) ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), oc4_codingProb μ σ (fun _ _ _ => (0 : ℝ)) x j) := by
-- proof
  apply StatMech.Walls.oc4_scale_sum_nonvacuous μ σ Λ hne ru rv hru hrv u v hu hv

/--
[oc4_scale_sum_empty_scales](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean)
-/
@[path]
private lemma oc4_scale_sum_empty_scales_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {σ : Fin 0 → E}
  {g : α → ℕ → ConfigSpace E → ℝ}
  {Λ : Finset α}
  {u v : α}
  {qu qv : ℕ → ℝ}
-- given
  (hg : ∀ x j ω, 0 ≤ g x j ω)
  (hne : Λ.Nonempty)
  (hu : u ∈ Λ)
  (hv : v ∈ Λ)
  (hcompu : ∀ k, qu k ≤ oc4_codingProb μ σ g u ((k : ℤ) - (0 : ℤ)).natAbs)
  (hcompv : ∀ k, qv k ≤ oc4_codingProb μ σ g v ((k : ℤ) - (0 : ℤ)).natAbs) :
-- imply
  ∑ k ∈ Finset.Icc 1 0, (qu k + qv k) ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (0 + 1), oc4_codingProb μ σ g x j) := by
-- proof
  apply StatMech.Walls.oc4_scale_sum_empty_scales μ σ g hg Λ hne u v hu hv qu qv hcompu hcompv

/--
[oc4_fk_box_crossing_scale_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean)
-/
@[path]
private lemma oc4_fk_box_crossing_scale_sum_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n → Sym2 V}
  {g : α → ℕ → ConfigSpace (Sym2 V) → ℝ}
  {Λ : Finset α}
  {ru rv : ℕ}
  {u v : α}
  {qu qv : ℕ → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hg : ∀ x j ω, 0 ≤ g x j ω)
  (hne : Λ.Nonempty)
  (hru : ru ≤ n)
  (hrv : rv ≤ n)
  (hu : u ∈ Λ)
  (hv : v ∈ Λ)
  (hcompu : ∀ k, qu k ≤ ∫ uu, g u ((k : ℤ) - (ru : ℤ)).natAbs (codeMap (fkMass G p q) σ uu) ∂(Vcube n))
  (hcompv : ∀ k, qv k ≤ ∫ uu, g v ((k : ℤ) - (rv : ℤ)).natAbs (codeMap (fkMass G p q) σ uu) ∂(Vcube n)) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, (qu k + qv k) ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), ∫ uu, g x j (codeMap (fkMass G p q) σ uu) ∂(Vcube n)) := by
-- proof
  apply StatMech.Walls.oc4_fk_box_crossing_scale_sum G hp hp1 hq σ g hg Λ hne ru rv hru hrv u v hu hv qu qv hcompu hcompv


-- created on 2026-10-23
