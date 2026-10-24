import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.SharpnessUncond
open Finset Real Set StatMech.Lattice StatMech StatMech.OSSS


/--
[liftCfg_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma liftCfg_monotone_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {edge : E → Sym2 (Site d)} :
-- imply
  Monotone (liftCfg edge) := by
-- proof
  apply StatMech.OSSS.liftCfg_monotone edge

/--
[openSubgraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma openSubgraph_mono_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ω₁ ω₂ : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ω₁ ≤ ω₂) :
-- imply
  openSubgraph d ω₁ ≤ openSubgraph d ω₂ := by
-- proof
  apply StatMech.OSSS.openSubgraph_mono h

/--
[connected_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma connected_mono_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ω₁ ω₂ : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : ω₁ ≤ ω₂)
  (hc : Connected d ω₁ x y) :
-- imply
  Connected d ω₂ x y := by
-- proof
  apply StatMech.OSSS.connected_mono h hc

/--
[connectedToSet_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma connectedToSet_mono_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {o : Site d}
  {B : Set (Site d)}
  {ω₁ ω₂ : ConfigSpace E}
-- given
  (h : ω₁ ≤ ω₂)
  (hc : ConnectedToSet d (liftCfg edge ω₁) o B) :
-- imply
  ConnectedToSet d (liftCfg edge ω₂) o B := by
-- proof
  apply StatMech.OSSS.connectedToSet_mono h hc

/--
[connectedToSet_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma connectedToSet_increasing_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {o : Site d}
  {B : Set (Site d)} :
-- imply
  IsIncreasing {ω : ConfigSpace E | ConnectedToSet d (liftCfg edge ω) o B} := by
-- proof
  apply StatMech.OSSS.connectedToSet_increasing edge o B

/--
[evalR_completeTree_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma evalR_completeTree_eq_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {B : Set (Site d)}
  {l : List E}
  {disc₀ : Finset (Site d)}
-- given
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : ∀ e, e ∈ l)
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hBdisc : ∀ b ∈ B, b ∈ disc₀) :
-- imply
  (completeTree endU endV o l disc₀).evalR = (crossEvent edge o B).indicator (fun _ => (1 : ℝ)) := by
-- proof
  apply StatMech.OSSS.evalR_completeTree_eq_indicator hinj hcoh hadj o B l hl disc₀ hdisc₀ hBdisc

/--
[covSum_ge_explore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma covSum_ge_explore_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  [Fintype κ]
  [Nonempty κ]
  {ν : E → Bool → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {l : List E}
  {B : Set (Site d)}
  {disc₀ : κ → Finset (Site d)}
  {R : κ → E → ℝ}
  {c₀ : ℝ}
  {D : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : ∀ e, e ∈ l)
  (hdisc₀ : ∀ k, ∀ x ∈ disc₀ k, x ∈ B)
  (hBdisc : ∀ k, ∀ b ∈ B, b ∈ disc₀ k)
  (hRdef : ∀ k e, R k e = expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) B then (1 : ℝ) else 0) + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) B then (1 : ℝ) else 0))
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDnn : 0 ≤ D)
  (hD : ∀ e, (∑ k, R k e) ≤ D) :
-- imply
  (Fintype.card κ : ℝ) * c₀ * (expect ν ((crossEvent edge o B).indicator (fun _ => (1 : ℝ))) * (1 - expect ν ((crossEvent edge o B).indicator (fun _ => (1 : ℝ))))) ≤ D * ∑ e, cov ν (coordI e) ((crossEvent edge o B).indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.OSSS.covSum_ge_explore hν hinj hcoh hadj o l hl B disc₀ hdisc₀ hBdisc R hRdef c₀ hc₀nn hc₀ D hDnn hD

/--
[osss_differential_inequality_disch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma osss_differential_inequality_disch_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {n : ℕ}
  {c₀ cR D θ θ' S : ℝ}
-- given
  (hD : 0 < D)
  (hcR : 0 < cR)
  (hcov : (n : ℝ) * c₀ * (θ * (1 - θ)) ≤ D * S)
  (hRussoEq : θ' = cR * S) :
-- imply
  (n : ℝ) * c₀ * cR / D * (θ * (1 - θ)) ≤ θ' := by
-- proof
  apply StatMech.OSSS.osss_differential_inequality_disch n c₀ cR D θ θ' S hD hcR hcov hRussoEq

/--
[fk_russo_discharges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma fk_russo_discharges_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < FK.russoPrefactor p ∧ FK.russoPrefactor p * (∑ e ∈ G.edgeFinset, FK.fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)) ≤ deriv (fun p => FK.fkProbOf G p q A) p := by
-- proof
  apply StatMech.OSSS.fk_russo_discharges G hp hp1 hq A

/--
[osss_subcritical_decay_disch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma osss_subcritical_decay_disch_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {a b rate : ℝ}
  {θn θn' : ℝ → ℝ}
-- given
  (hab : a < b)
  (hrate : 0 < rate)
  (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
  (hineq : ∀ x ∈ Icc a b, rate * θn x ≤ θn' x)
  (hθa : 0 ≤ θn a)
  (hθb : θn b ≤ 1) :
-- imply
  0 ≤ θn a ∧ θn a ≤ Real.exp (-(rate * (b - a))) ∧ Real.exp (-(rate * (b - a))) < 1 := by
-- proof
  apply StatMech.OSSS.osss_subcritical_decay_disch a b rate hab hrate θn θn' hd hineq hθa hθb

/--
[osss_subcritical_decay_box_disch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean)
-/
@[path]
private lemma osss_subcritical_decay_box_disch_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {a b c : ℝ}
  {n : ℕ}
  {θn θn' : ℝ → ℝ}
-- given
  (hab : a < b)
  (hc : 0 < c)
  (hn : 1 ≤ n)
  (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
  (hineq : ∀ x ∈ Icc a b, (c * n) * θn x ≤ θn' x)
  (hθa : 0 ≤ θn a)
  (hθb : θn b ≤ 1) :
-- imply
  θn a ≤ Real.exp (-(c * n * (b - a))) := by
-- proof
  apply StatMech.OSSS.osss_subcritical_decay_box_disch a b c n hab hc hn θn θn' hd hineq hθa hθb


-- created on 2026-10-23
