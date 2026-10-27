import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.GrandCoupling


/--
[condProbBit_true_eq_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma condProbBit_true_eq_open_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
  {e : E} :
-- imply
  condProbBit μ F η e true = condProbOpen μ F η e := by
-- proof
  apply StatMech.OSSS.GrandCoupling.condProbBit_true_eq_open μ F η e

/--
[condProbClosed_eq_one_sub_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma condProbClosed_eq_one_sub_open_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
  {e : E}
-- given
  (hF : 0 < condNorm μ F η) :
-- imply
  condProbClosed μ F η e = 1 - condProbOpen μ F η e := by
-- proof
  apply StatMech.OSSS.GrandCoupling.condProbClosed_eq_one_sub_open μ F η e hF

/--
[condProbClosed_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma condProbClosed_antitone_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {ξ ζ : ConfigSpace E}
-- given
  (hmono : IsMonotonicMeasure μ)
  (hle : ∀ f ∈ F, ξ f ≤ ζ f)
  (hZξ : 0 < condNorm μ F ξ)
  (hZζ : 0 < condNorm μ F ζ) :
-- imply
  condProbClosed μ F ζ e ≤ condProbClosed μ F ξ e := by
-- proof
  apply StatMech.OSSS.GrandCoupling.condProbClosed_antitone hmono F e ξ ζ hle hZξ hZζ

/--
[decide_ge_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma decide_ge_mono_eq
  [Fintype E]
  [DecidableEq E]
  {a a' thr thr' : ℝ}
-- given
  (ha : a ≤ a')
  (hthr : thr' ≤ thr) :
-- imply
  decide (a ≥ thr) ≤ decide (a' ≥ thr') := by
-- proof
  apply StatMech.OSSS.GrandCoupling.decide_ge_mono ha hthr

/--
[codePrefix_mono_u](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma codePrefix_mono_u_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u u' : Fin n → ℝ}
  {k : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hle : u ≤ u') :
-- imply
  codePrefix μ σ u k ≤ codePrefix μ σ u' k := by
-- proof
  apply StatMech.OSSS.GrandCoupling.codePrefix_mono_u hpos hmono σ u u' hle k

/--
[codeMap_mono_u](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma codeMap_mono_u_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ) :
-- imply
  Monotone (fun u : Fin n → ℝ => codeMap μ σ u) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.codeMap_mono_u hpos hmono σ

/--
[measurable_codeMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma measurable_codeMap_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E} :
-- imply
  Measurable (fun u : Fin n → ℝ => codeMap μ (σ : Fin n → E) u) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.measurable_codeMap μ σ

/--
[measurable_g_codeMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma measurable_g_codeMap_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ} :
-- imply
  Measurable (fun u : Fin n → ℝ => g (codeMap μ (σ : Fin n → E) u)) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.measurable_g_codeMap μ σ g

/--
[vcube_rawInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma vcube_rawInterval_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {x : ConfigSpace E}
  {t : Fin n}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  (volume.restrict (Set.Icc (0:ℝ) 1) (rawInterval μ σ x t)).toReal = condProbBit μ (prefixSet σ (t : ℕ)) x (σ t) (x (σ t)) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.vcube_rawInterval μ hpos σ x t

/--
[codeMap_fibre_eq_rawbox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma codeMap_fibre_eq_rawbox_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E} :
-- imply
  {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x} = Set.univ.pi (fun t => rawInterval μ (σ : Fin n → E) x t) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.codeMap_fibre_eq_rawbox μ σ x

/--
[vcube_fibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma vcube_fibre_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal = μ x := by
-- proof
  apply StatMech.OSSS.GrandCoupling.vcube_fibre μ hpos hμ1 σ x

/--
[integral_g_codeMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma integral_g_codeMap_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.OSSS.GrandCoupling.integral_g_codeMap μ hpos hμ1 σ g

/--
[Wt_mono_V](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma Wt_mono_V_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U : Fin n → ℝ}
  {s : ℕ} :
-- imply
  Monotone (fun V : Fin n → ℝ => Wt U V s) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.Wt_mono_V U s

/--
[measurable_Wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma measurable_Wt_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U : Fin n → ℝ}
  {s : ℕ} :
-- imply
  Measurable (fun V : Fin n → ℝ => Wt U V s) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.measurable_Wt U s

/--
[f_codeMap_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma f_codeMap_mono_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ}
  {s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f) :
-- imply
  Monotone (fun V : Fin n → ℝ => f (codeMap μ σ (Wt U V s))) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.f_codeMap_mono hpos hmono σ hf U s

/--
[coord_codeMap_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma coord_codeMap_mono_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {e : E}
  {U : Fin n → ℝ}
  {s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ) :
-- imply
  Monotone (fun V : Fin n → ℝ => Lindeberg.coord e (codeMap μ σ (Wt U V s))) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.coord_codeMap_mono hpos hmono σ e U s

/--
[measurable_f_codeMap_Wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma measurable_f_codeMap_Wt_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ}
  {s : ℕ} :
-- imply
  Measurable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (Wt U V s))) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.measurable_f_codeMap_Wt μ σ f U s

/--
[measurable_coord_codeMap_Wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma measurable_coord_codeMap_Wt_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {e : E}
  {U : Fin n → ℝ}
  {s : ℕ} :
-- imply
  Measurable (fun V : Fin n → ℝ => Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s))) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.measurable_coord_codeMap_Wt μ σ e U s

/--
[abs_coord_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma abs_coord_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  |Lindeberg.coord e ω| ≤ 1 := by
-- proof
  apply StatMech.OSSS.GrandCoupling.abs_coord_le_one e ω

/--
[grandCoupling_fkg_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma grandCoupling_fkg_cross_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {U : Fin n → ℝ}
  {s₁ s₂ : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁)) ∂(Vcube n)) * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n)) ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.grandCoupling_fkg_cross hpos hmono σ hf hfC e U s₁ s₂

/--
[osss_grand_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma osss_grand_coupling_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {U : Fin n → ℝ}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  ((∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n)) * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) ∧ ((∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n)) ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.osss_grand_coupling hpos hmono σ hf hfC e U t

/--
[fk_codeMap_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma fk_codeMap_mono_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n → Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Monotone (fun u : Fin n → ℝ => codeMap (fkMass G p q) σ u) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.fk_codeMap_mono G hp hp1 hq σ

/--
[fk_grandCoupling_fkg_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean)
-/
@[path]
private lemma fk_grandCoupling_fkg_cross_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {Cf : ℝ}
  {e : Sym2 V}
  {U : Fin n → ℝ}
  {s₁ s₂ : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  (∫ Vv, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₁)) ∂(Vcube n)) * (∫ Vv, Lindeberg.coord e (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₂)) ∂(Vcube n)) ≤ ∫ Vv, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₁)) * Lindeberg.coord e (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₂)) ∂(Vcube n) := by
-- proof
  apply StatMech.OSSS.GrandCoupling.fk_grandCoupling_fkg_cross G hp hp1 hq σ hf hfC e U s₁ s₂


-- created on 2026-10-23
