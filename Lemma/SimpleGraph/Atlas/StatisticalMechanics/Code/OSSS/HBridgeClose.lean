import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.HBridgeClose.Part2
open Finset Real Set Filter Topology StatMech StatMech.OSSS StatMech.OSSS.HBridgeClose


/--
[flipE_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma flipE_self_eq
  [Fintype V]
  [DecidableEq V]
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  flipE e ω e = !ω e := by
-- proof
  apply StatMech.OSSS.HBridgeClose.flipE_self e ω

/--
[flipE_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma flipE_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {e e' : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (h : e' ≠ e) :
-- imply
  flipE e ω e' = ω e' := by
-- proof
  apply StatMech.OSSS.HBridgeClose.flipE_of_ne h ω

/--
[flipE_flipE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma flipE_flipE_eq
  [Fintype V]
  [DecidableEq V]
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  flipE e (flipE e ω) = ω := by
-- proof
  apply StatMech.OSSS.HBridgeClose.flipE_flipE e ω

/--
[flipEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma flipEquiv_apply_eq
  [Fintype V]
  [DecidableEq V]
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  flipEquiv e ω = flipE e ω := by
-- proof
  apply StatMech.OSSS.HBridgeClose.flipEquiv_apply e ω

/--
[coord_add_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma coord_add_flip_eq
  [Fintype V]
  [DecidableEq V]
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  coord e ω + coord e (flipE e ω) = 1 := by
-- proof
  apply StatMech.OSSS.HBridgeClose.coord_add_flip e ω

/--
[mean_mul_coord_of_flip_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma mean_mul_coord_of_flip_invariant_eq
  [Fintype V]
  [DecidableEq V]
  {μ : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hμ : ∀ ω, μ (flipE e ω) = μ ω)
  (hf : ∀ ω, f (flipE e ω) = f ω) :
-- imply
  Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) = Lindeberg.mean μ f / 2 := by
-- proof
  apply StatMech.OSSS.HBridgeClose.mean_mul_coord_of_flip_invariant μ e hμ f hf

/--
[cov_coord_of_flip_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma cov_coord_of_flip_invariant_eq
  [Fintype V]
  [DecidableEq V]
  {μ : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hμ1 : ∑ ω, μ ω = 1)
  (hμ : ∀ ω, μ (flipE e ω) = μ ω)
  (hf : ∀ ω, f (flipE e ω) = f ω) :
-- imply
  Lindeberg.cov μ f (Lindeberg.coord e) = 0 := by
-- proof
  apply StatMech.OSSS.HBridgeClose.cov_coord_of_flip_invariant μ hμ1 e hμ f hf

/--
[covariance_support_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma covariance_support_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {μ : ConfigSpace (Sym2 V) → ℝ}
  {S : Finset (Sym2 V)}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hμ1 : ∑ ω, μ ω = 1)
  (hμ : ∀ e ∉ S, ∀ ω, μ (flipE e ω) = μ ω)
  (hf : ∀ e ∉ S, ∀ ω, f (flipE e ω) = f ω) :
-- imply
  ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) = ∑ e ∈ S, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.HBridgeClose.covariance_support_bridge μ hμ1 S f hμ hf

/--
[openSub_flipE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma openSub_flipE_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ G.edgeFinset) :
-- imply
  openSub G (flipE e ω) = openSub G ω := by
-- proof
  apply StatMech.OSSS.HBridgeClose.openSub_flipE G p q he ω

/--
[fkWeight_flipE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma fkWeight_flipE_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ G.edgeFinset) :
-- imply
  fkWeight G p q (flipE e ω) = fkWeight G p q ω := by
-- proof
  apply StatMech.OSSS.HBridgeClose.fkWeight_flipE G p q he ω

/--
[hbg_fkProb_flipE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma hbg_fkProb_flipE_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ G.edgeFinset) :
-- imply
  fkProb G p q (flipE e ω) = fkProb G p q ω := by
-- proof
  apply StatMech.OSSS.HBridgeClose.hbg_fkProb_flipE G p q he ω

/--
[fkMean_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma fkMean_flip_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V} :
-- imply
  fkMean G p q g = ∑ ω, g (flipE e ω) * fkProb G p q (flipE e ω) := by
-- proof
  apply StatMech.OSSS.HBridgeClose.fkMean_flip G p q g e

/--
[fkMean_mul_coord_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma fkMean_mul_coord_off_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (he : e ∉ G.edgeFinset)
  (hf : ∀ ω, f (flipE e ω) = f ω) :
-- imply
  fkMean G p q (fun ω => f ω * coord e ω) = fkMean G p q f / 2 := by
-- proof
  apply StatMech.OSSS.HBridgeClose.fkMean_mul_coord_off G p q he f hf

/--
[fkMean_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma fkMean_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkMean G p q (fun _ => (1 : ℝ)) = 1 := by
-- proof
  apply StatMech.OSSS.HBridgeClose.fkMean_one G p q hp hp1 hq

/--
[hbg_fkCov_coord_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma hbg_fkCov_coord_off_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (he : e ∉ G.edgeFinset)
  (hf : ∀ ω, f (flipE e ω) = f ω) :
-- imply
  fkCov G p q f (coord e) = 0 := by
-- proof
  apply StatMech.OSSS.HBridgeClose.hbg_fkCov_coord_off G p q hp hp1 hq he f hf

/--
[hbg_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma hbg_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hf : ∀ e ∉ G.edgeFinset, ∀ ω, f (flipE e ω) = f ω) :
-- imply
  ∑ e, fkCov G p q f (coord e) = ∑ e ∈ G.edgeFinset, fkCov G p q f (coord e) := by
-- proof
  apply StatMech.OSSS.HBridgeClose.hbg_bridge G p q hp hp1 hq f hf

/--
[hbg_event_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma hbg_event_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hA : ∀ e ∉ G.edgeFinset, ∀ ω, (flipE e ω ∈ A ↔ ω ∈ A)) :
-- imply
  ∑ e, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e) = ∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (coord e) := by
-- proof
  apply StatMech.OSSS.HBridgeClose.hbg_event_bridge G p q hp hp1 hq A hA

/--
[hbg_connEvent_offGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma hbg_connEvent_offGraph_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x y : V}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ G.edgeFinset) :
-- imply
  flipE e ω ∈ connEvent G x y ↔ ω ∈ connEvent G x y := by
-- proof
  apply StatMech.OSSS.HBridgeClose.hbg_connEvent_offGraph G p q he ω

/--
[hbg_connEvent_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma hbg_connEvent_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x y : V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ e, fkCov G p q ((connEvent G x y).indicator (fun _ => (1 : ℝ))) (coord e) = ∑ e ∈ G.edgeFinset, fkCov G p q ((connEvent G x y).indicator (fun _ => (1 : ℝ))) (coord e) := by
-- proof
  apply StatMech.OSSS.HBridgeClose.hbg_connEvent_bridge G p q hp hp1 hq x y

/--
[hbg_fk_q2_subcritical_decay_connEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma hbg_fk_q2_subcritical_decay_connEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x y : V}
  {a b κ : ℝ}
-- given
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hκ : 0 < κ)
  (hθub : ∀ s ∈ Icc a b, fkProbOf G s 2 (connEvent G x y) ≤ 1 - κ) :
-- imply
  fkProbOf G a 2 (connEvent G x y) ≤ Real.exp (-(4 * κ * (b - a))) := by
-- proof
  apply StatMech.OSSS.HBridgeClose.hbg_fk_q2_subcritical_decay_connEvent G p q x y a b κ hab ha0 hb1 hκ hθub

/--
[hbg_fk_q2_sharpness_connEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma hbg_fk_q2_sharpness_connEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x y : V}
  {a b κ : ℝ}
  {T : ℕ → ℝ → ℝ}
  {mseq : ℕ → ℝ}
  {β' β fβ fβ' m : ℝ}
  {Θ : ℝ → ℝ}
  {β₁ : ℝ}
-- given
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hκ : 0 < κ)
  (hθub : ∀ s ∈ Icc a b, fkProbOf G s 2 (connEvent G x y) ≤ 1 - κ)
  (hββ : β' ≤ β)
  (hm1 : 1 ≤ m)
  (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
  (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
  (hmlim : Tendsto mseq atTop (𝓝 m))
  (hboundMF : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β')
  (hP1 : ∀ b₀, b₀ < β₁ → Θ b₀ = 0)
  (hP2 : ∀ b₀, β₁ < b₀ → 0 < Θ b₀) :
-- imply
  (fkProbOf G a 2 (connEvent G x y) ≤ Real.exp (-(4 * κ * (b - a)))) ∧ (β - β' ≤ fβ - fβ') ∧ sSup (bcm_subcriticalSet Θ) = β₁ := by
-- proof
  apply StatMech.OSSS.HBridgeClose.hbg_fk_q2_sharpness_connEvent G p q x y a b κ hab ha0 hb1 hκ hθub T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hboundMF Θ β₁ hP1 hP2

/--
[hbg_potts_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean)
-/
@[path]
private lemma hbg_potts_decay_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {q : ℝ}
  {c pottsCorr θ : ℝ}
-- given
  (hq : 2 ≤ q)
  (hES : pottsCorr = (q - 1) / q * θ)
  (hθ_nonneg : 0 ≤ θ)
  (hθ_decay : θ ≤ Real.exp (-c)) :
-- imply
  0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-c) := by
-- proof
  apply StatMech.OSSS.HBridgeClose.hbg_potts_decay G p q q hq c pottsCorr θ hES hθ_nonneg hθ_decay


-- created on 2026-10-23
