import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.GrandCouplingAssembly.Part6
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.GrandCouplingAssembly


/--
[codePrefix_congr_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma codePrefix_congr_of_agree_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u u' : Fin n → ℝ}
  {m : ℕ}
-- given
  (hm : m ≤ n)
  (h : ∀ i : Fin n, (i : ℕ) < m → u i = u' i) :
-- imply
  codePrefix μ σ u m = codePrefix μ σ u' m := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.codePrefix_congr_of_agree μ σ u u' m hm h

/--
[codePrefix_step_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma codePrefix_step_congr_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u u' : Fin n → ℝ}
  {m : ℕ}
-- given
  (hmn : m < n)
  (hpre : codePrefix μ σ u m = codePrefix μ σ u' m)
  (hum : u ⟨m, hmn⟩ = u' ⟨m, hmn⟩) :
-- imply
  codePrefix μ σ u (m+1) = codePrefix μ σ u' (m+1) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.codePrefix_step_congr μ σ u u' m hmn hpre hum

/--
[codePrefix_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma codePrefix_forward_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u u' : Fin n → ℝ}
  {start : ℕ}
-- given
  (hagree : ∀ i : Fin n, start ≤ (i : ℕ) → u i = u' i)
  (hstart : codePrefix μ σ u start = codePrefix μ σ u' start) :
-- imply
  ∀ m, start ≤ m → m ≤ n → codePrefix μ σ u m = codePrefix μ σ u' m := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.codePrefix_forward μ σ u u' start hagree hstart

/--
[codePrefix_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma codePrefix_det_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u u' : Fin n → ℝ}
  {k : ℕ}
-- given
  (hk : k < n)
  (hagree : ∀ i : Fin n, (i : ℕ) ≠ k → u i = u' i)
  (hbit : codePrefix μ σ u (k+1) (σ ⟨k, hk⟩) = codePrefix μ σ u' (k+1) (σ ⟨k, hk⟩)) :
-- imply
  ∀ m, m ≤ n → codePrefix μ σ u m = codePrefix μ σ u' m := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.codePrefix_det μ σ u u' k hk hagree hbit

/--
[codeMap_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma codeMap_det_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {u u' : Fin n → ℝ}
  {k : ℕ}
-- given
  (hσ : Function.Injective σ)
  (hk : k < n)
  (hagree : ∀ i : Fin n, (i : ℕ) ≠ k → u i = u' i)
  (hbit : codeMap μ σ u (σ ⟨k, hk⟩) = codeMap μ σ u' (σ ⟨k, hk⟩)) :
-- imply
  codeMap μ σ u = codeMap μ σ u' := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.codeMap_det μ σ hσ u u' k hk hagree hbit

/--
[Wt_agree_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma Wt_agree_off_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ}
  {t : ℕ}
-- given
  (ht : 1 ≤ t) :
-- imply
  ∀ i : Fin n, (i : ℕ) ≠ t - 1 → Wt U V t i = Wt U V (t-1) i := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.Wt_agree_off U V t ht

/--
[Wt_at_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma Wt_at_pos_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ}
  {t : ℕ}
-- given
  (ht : 1 ≤ t)
  (htn : t - 1 < n) :
-- imply
  Wt U V t ⟨t-1, htn⟩ = V ⟨t-1, htn⟩ ∧ Wt U V (t-1) ⟨t-1, htn⟩ = U ⟨t-1, htn⟩ := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.Wt_at_pos U V t ht htn

/--
[sw_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma sw_invol_eq
  [Fintype E]
  [DecidableEq E]
  {n s : ℕ} :
-- imply
  Function.Involutive (sw n s) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.sw_invol n s

/--
[swEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma swEquiv_symm_apply_eq
  [Fintype E]
  [DecidableEq E]
  {n s : ℕ}
  {x : Fin n ⊕ Fin n} :
-- imply
  (swEquiv n s).symm x = sw n s x := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.swEquiv_symm_apply n s x

/--
[combine_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma combine_apply_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ}
  {x : Fin n ⊕ Fin n} :
-- imply
  combine n (U, V) x = Sum.elim U V x := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.combine_apply n U V x

/--
[selMap_eq_Wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma selMap_eq_Wt_eq
  [Fintype E]
  [DecidableEq E]
  {n s : ℕ}
  {U V : Fin n → ℝ} :
-- imply
  selMap n s (U, V) = Wt U V s := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.selMap_eq_Wt n s U V

/--
[selMap_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma selMap_measurePreserving_eq
  [Fintype E]
  [DecidableEq E]
  {n s : ℕ} :
-- imply
  MeasurePreserving (selMap n s) ((Vcube n).prod (Vcube n)) (Vcube n) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.selMap_measurePreserving n s

/--
[integral_g_codeMap_Wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma integral_g_codeMap_Wt_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ p, g (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s)) ∂((Vcube n).prod (Vcube n)) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.integral_g_codeMap_Wt μ hpos hμ1 σ g s

/--
[Wt_mono_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma Wt_mono_prod_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {s : ℕ} :
-- imply
  Monotone (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Wt p.1 p.2 s) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.Wt_mono_prod s

/--
[f_codeMap_Wt_mono_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma f_codeMap_Wt_mono_prod_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {f : ConfigSpace E → ℝ}
  {s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f) :
-- imply
  Monotone (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (codeMap μ σ (Wt p.1 p.2 s))) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.f_codeMap_Wt_mono_prod hpos hmono σ hf s

/--
[coord_codeMap_Wt_mono_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma coord_codeMap_Wt_mono_prod_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n → E}
  {e : E}
  {s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ) :
-- imply
  Monotone (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Lindeberg.coord e (codeMap μ σ (Wt p.1 p.2 s))) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.coord_codeMap_Wt_mono_prod hpos hmono σ e s

/--
[measurable_g_codeMap_Wt_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma measurable_g_codeMap_Wt_prod_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {g : ConfigSpace E → ℝ}
  {s : ℕ} :
-- imply
  Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s))) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.measurable_g_codeMap_Wt_prod μ σ g s

/--
[comb2_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma comb2_measurePreserving_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ} :
-- imply
  MeasurePreserving (comb2 n) ((Vcube n).prod (Vcube n)) (Vcube (n+n)) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.comb2_measurePreserving n

/--
[comb2_symm_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma comb2_symm_fst_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {w : Fin (n+n) → ℝ}
  {i : Fin n} :
-- imply
  ((comb2 n).symm w).1 i = w (finSumFinEquiv (Sum.inl i)) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.comb2_symm_fst n w i

/--
[comb2_symm_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma comb2_symm_snd_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {w : Fin (n+n) → ℝ}
  {i : Fin n} :
-- imply
  ((comb2 n).symm w).2 i = w (finSumFinEquiv (Sum.inr i)) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.comb2_symm_snd n w i

/--
[comb2_symm_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma comb2_symm_mono_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ} :
-- imply
  Monotone (comb2 n).symm := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.comb2_symm_mono n

/--
[hasFKG_prod_Vcube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma hasFKG_prod_Vcube_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ} :
-- imply
  HasFKG ((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.hasFKG_prod_Vcube n

/--
[abs_coord_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
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
  apply StatMech.OSSS.GrandCouplingAssembly.abs_coord_le_one e ω

/--
[grandCoupling_fkg_cross_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma grandCoupling_fkg_cross_prod_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {s₁ s₂ : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  (∫ p, f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁)) ∂((Vcube n).prod (Vcube n))) * (∫ p, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂)) ∂((Vcube n).prod (Vcube n))) ≤ ∫ p, f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂)) ∂((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.grandCoupling_fkg_cross_prod hpos hmono σ hf hfC e s₁ s₂

/--
[coord_eq01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma coord_eq01_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  Lindeberg.coord e ω = 0 ∨ Lindeberg.coord e ω = 1 := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.coord_eq01 e ω

/--
[tt_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma tt_algebra_eq
  [Fintype E]
  [DecidableEq E]
  {a b p q : ℝ}
-- given
  (hp : p = 0 ∨ p = 1)
  (hq : q = 0 ∨ q = 1)
  (hcmp : (b ≤ a ∧ q ≤ p) ∨ (a ≤ b ∧ p ≤ q))
  (hdet : p = q → a = b) :
-- imply
  |a - b| = b * q + a * p - b * p - a * q := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.tt_algebra a b p q hp hq hcmp hdet

/--
[abs_step_eq_four_terms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma abs_step_eq_four_terms_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {U V : Fin n → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (ht : 1 ≤ t)
  (htn : t - 1 < n) :
-- imply
  |f (codeMap μ (σ : Fin n → E) (Wt U V t)) - f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))| = f (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) + f (codeMap μ (σ : Fin n → E) (Wt U V t)) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V t)) - f (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V t)) - f (codeMap μ (σ : Fin n → E) (Wt U V t)) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.abs_step_eq_four_terms hpos hmono σ hf t ht htn U V

/--
[integrable_prod_obs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma integrable_prod_obs_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {s₁ s₂ : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂))) ((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.integrable_prod_obs μ σ hfC e s₁ s₂

/--
[sum_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma sum_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  ∑ x, g x * μ x = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.sum_eq_mean μ g

/--
[step_le_two_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma step_le_two_cov_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf)
  (ht : 1 ≤ t)
  (htn : t - 1 < n) :
-- imply
  (∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t)) - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t-1)))| ∂((Vcube n).prod (Vcube n))) ≤ 2 * Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.step_le_two_cov hpos hμ1 hmono σ hf hfC t ht htn

/--
[Wt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma Wt_zero_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ} :
-- imply
  Wt U V 0 = U := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.Wt_zero U V

/--
[Wt_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma Wt_card_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {U V : Fin n → ℝ} :
-- imply
  Wt U V n = V := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.Wt_card U V

/--
[integral_two_codeMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma integral_two_codeMap_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {Ch : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (h : ConfigSpace E → ConfigSpace E → ℝ)
  (hC : ∀ x y, |h x y| ≤ Ch) :
-- imply
  ∫ p, h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2) ∂((Vcube n).prod (Vcube n)) = ∑ x, (∑ y, h x y * μ y) * μ x := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.integral_two_codeMap μ hpos hμ1 σ h hC

/--
[abs_f_diff_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma abs_f_diff_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E → ℝ}
  {x y : ConfigSpace E}
-- given
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  |f x - f y| ≤ 1 := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.abs_f_diff_le_one hf0 hf1 x y

/--
[var_le_grandCoupling_first_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma var_le_grandCoupling_first_step_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  Lindeberg.var μ f ≤ (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0)) - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n))| ∂((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.var_le_grandCoupling_first_step hpos hμ1 σ hf0 hf1

/--
[grandCoupling_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma grandCoupling_telescope_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
-- given
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  (∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0)) - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n))| ∂((Vcube n).prod (Vcube n))) ≤ ∑ t ∈ Finset.range n, ∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t+1))) - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t))| ∂((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.grandCoupling_telescope σ hfC

/--
[tree_osss_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma tree_osss_unconditional_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  Lindeberg.var μ f ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.tree_osss_unconditional hpos hμ1 hmono hf hf0 hf1

/--
[osss_monotonicOSSSBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma osss_monotonicOSSSBound_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  MonotonicOSSSBound μ Finset.univ f 1 1 1 := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.osss_monotonicOSSSBound hpos hμ1 hmono hf hf0 hf1

/--
[fk_q2_osss](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma fk_q2_osss_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  Lindeberg.var (fkMass G p 2) f ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.fk_q2_osss G hp hp1 hf hf0 hf1

/--
[fk_q2_monotonicOSSSBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean)
-/
@[path]
private lemma fk_q2_monotonicOSSSBound_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  MonotonicOSSSBound (fkMass G p 2) Finset.univ f 1 1 1 := by
-- proof
  apply StatMech.OSSS.GrandCouplingAssembly.fk_q2_monotonicOSSSBound G hp hp1 hf hf0 hf1


-- created on 2026-10-23
