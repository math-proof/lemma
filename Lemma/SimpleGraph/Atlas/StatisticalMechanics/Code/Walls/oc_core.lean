import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc_core.Part3
open Finset StatMech StatMech.Walls


/--
[oc_perScaleRevealment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_perScaleRevealment_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {n : ℕ}
  {l : List E}
  {discF : ℕ → Finset (Site d)}
  {k : ℕ}
  {e : E}
-- given
  (hν : IsProbWeight ν)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hdisc : ∀ k, ∀ x ∈ discF k, x ∈ vertexBoundary d k) :
-- imply
  reveal ν (oc_clusterTree endU endV o n l discF k) e ≤ (expect ν fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + (expect ν fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Walls.oc_perScaleRevealment hν hinj hcoh hadj o n l discF hdisc k e

/--
[oc_perScaleRevealment_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_perScaleRevealment_family_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {n : ℕ}
  {l : List E}
  {discF : ℕ → Finset (Site d)}
  {kscale : κ → ℕ}
  {k : κ}
  {e : E}
-- given
  (hν : IsProbWeight ν)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hdisc : ∀ k, ∀ x ∈ discF k, x ∈ vertexBoundary d k) :
-- imply
  reveal ν (oc_clusterTree endU endV o n l discF (kscale k)) e ≤ (expect ν fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d (kscale k)) then (1 : ℝ) else 0) + (expect ν fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d (kscale k)) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Walls.oc_perScaleRevealment_family hν hinj hcoh hadj o n l discF hdisc kscale k e

/--
[oc_familyTrees_compute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_familyTrees_compute_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {n : ℕ}
  {l : List E}
  {discF : ℕ → Finset (Site d)}
  {k : ℕ}
  {ω : ConfigSpace E}
  [Decidable (ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n))]
-- given
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : ∀ e, e ∈ l)
  (hk : 1 ≤ k)
  (hkn : k ≤ n)
  (ho : o ∈ box d (k - 1))
  (hBdisc : ∀ b ∈ vertexBoundary d k, b ∈ discF k)
  (hoB : o ∉ discF k) :
-- imply
  (oc_clusterTree endU endV o n l discF k).evalR ω = if ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n) then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.Walls.oc_familyTrees_compute hinj hcoh hadj o n l hl discF k hk hkn ho hBdisc hoB ω

/--
[oc_familyAveraged_covLowerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_familyAveraged_covLowerBound_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)}
  [Fintype κ]
  [Nonempty κ]
  {T : κ → DecisionTree E}
  {R : κ → E → ℝ}
  {c₀ : ℝ}
  {D : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
  (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDnn : 0 ≤ D)
  (hsum : ∀ e, (∑ k, R k e) ≤ D) :
-- imply
  (Fintype.card κ : ℝ) * c₀ * (expect ν (A.indicator (fun _ => (1 : ℝ))) * (1 - expect ν (A.indicator (fun _ => (1 : ℝ))))) ≤ D * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.Walls.oc_familyAveraged_covLowerBound hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum

/--
[oc_familyAveraged_covLowerBound_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_familyAveraged_covLowerBound_div_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)}
  [Fintype κ]
  [Nonempty κ]
  {T : κ → DecisionTree E}
  {R : κ → E → ℝ}
  {c₀ : ℝ}
  {D : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
  (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDpos : 0 < D)
  (hsum : ∀ e, (∑ k, R k e) ≤ D) :
-- imply
  ((Fintype.card κ : ℝ) * c₀ / D) * (expect ν (A.indicator (fun _ => (1 : ℝ))) * (1 - expect ν (A.indicator (fun _ => (1 : ℝ))))) ≤ ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.Walls.oc_familyAveraged_covLowerBound_div hν hA T hT R hreach c₀ hc₀nn hc₀ D hDpos hsum

/--
[oc_scaleSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_scaleSum_le_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {n : ℕ}
  {μTrans : Site d → ℕ → ℝ}
  {Λ : Finset (Site d)}
  {rdist : Site d → ℕ}
  {e : E}
-- given
  (hμ : ∀ x j, 0 ≤ μTrans x j)
  (hΛne : Λ.Nonempty)
  (hru : endU e ∈ Λ)
  (hrv : endV e ∈ Λ)
  (hruN : rdist (endU e) ≤ n)
  (hrvN : rdist (endV e) ≤ n)
  (hcompu : ∀ k, (expect ν fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μTrans (endU e) ((k : ℤ) - (rdist (endU e) : ℤ)).natAbs)
  (hcompv : ∀ k, (expect ν fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μTrans (endV e) ((k : ℤ) - (rdist (endV e) : ℤ)).natAbs) :
-- imply
  (∑ k : oc_ScaleIdx n, oc_Rscale (ν := ν) edge endU endV n k e) ≤ 4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j) := by
-- proof
  apply StatMech.Walls.oc_scaleSum_le edge endU endV n μTrans hμ Λ hΛne rdist e hru hrv hruN hrvN hcompu hcompv

/--
[oc_corOSSS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_corOSSS_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {n : ℕ}
  {l : List E}
  {discF : ℕ → Finset (Site d)}
  {c₀ : ℝ}
  {μTrans : Site d → ℕ → ℝ}
  {Λ : Finset (Site d)}
  {rdist : Site d → ℕ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hn : 1 ≤ n)
  (hdisc : ∀ k, ∀ x ∈ discF k, x ∈ vertexBoundary d k)
  (hT : ∀ k : oc_ScaleIdx n, (oc_clusterTree endU endV o n l discF k.1).evalR = A.indicator (fun _ => (1 : ℝ)))
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hμ : ∀ x j, 0 ≤ μTrans x j)
  (hΛne : Λ.Nonempty)
  (hru : ∀ e, endU e ∈ Λ)
  (hrv : ∀ e, endV e ∈ Λ)
  (hruN : ∀ e, rdist (endU e) ≤ n)
  (hrvN : ∀ e, rdist (endV e) ≤ n)
  (hcompu : ∀ e k, (expect ν fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μTrans (endU e) ((k : ℤ) - (rdist (endU e) : ℤ)).natAbs)
  (hcompv : ∀ e k, (expect ν fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μTrans (endV e) ((k : ℤ) - (rdist (endV e) : ℤ)).natAbs) :
-- imply
  (Fintype.card (oc_ScaleIdx n) : ℝ) * c₀ * (expect ν (A.indicator (fun _ => (1 : ℝ))) * (1 - expect ν (A.indicator (fun _ => (1 : ℝ))))) ≤ (4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j)) * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.Walls.oc_corOSSS hν hA hinj hcoh hadj o n hn l discF hdisc hT c₀ hc₀nn hc₀ μTrans hμ Λ hΛne rdist hru hrv hruN hrvN hcompu hcompv

/--
[oc_sharp_covLowerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_sharp_covLowerBound_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)}
  [Fintype κ]
  [Nonempty κ]
  {T : κ → DecisionTree E}
  {R : κ → E → ℝ}
  {c₀ : ℝ}
  {D Sn : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
  (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDnn : 0 ≤ D)
  (hsum : ∀ e, (∑ k, R k e) ≤ D)
  (hDS : D ≤ 8 * Sn)
  (hcovnn : 0 ≤ ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ)))) :
-- imply
  (Fintype.card κ : ℝ) * c₀ * (expect ν (A.indicator (fun _ => (1 : ℝ))) * (1 - expect ν (A.indicator (fun _ => (1 : ℝ))))) ≤ (8 * Sn) * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.Walls.oc_sharp_covLowerBound hν hA T hT R hreach c₀ hc₀nn hc₀ D Sn hDnn hsum hDS hcovnn

/--
[oc_fourD_le_eight_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_fourD_le_eight_S_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {β : ℝ}
  {D : ℝ}
-- given
  (hD : D ≤ 2 * oc_S Gf Af n β) :
-- imply
  4 * D ≤ 8 * oc_S Gf Af n β := by
-- proof
  apply StatMech.Walls.oc_fourD_le_eight_S Gf Af n β D hD

/--
[oc_correlated_covLowerBound_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_correlated_covLowerBound_of_bridge_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)}
  [Fintype κ]
  [Nonempty κ]
  {T : κ → DecisionTree E}
  {R : κ → E → ℝ}
  {c₀ : ℝ}
  {D : ℝ}
  {θμ covCorr : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
  (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDnn : 0 ≤ D)
  (hsum : ∀ e, (∑ k, R k e) ≤ D)
  (hbridge : oc_CodingCovBridge (ν := ν) (A.indicator (fun _ => (1 : ℝ))) θμ covCorr) :
-- imply
  (Fintype.card κ : ℝ) * c₀ * (θμ * (1 - θμ)) ≤ D * covCorr := by
-- proof
  apply StatMech.Walls.oc_correlated_covLowerBound_of_bridge hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum θμ covCorr hbridge

/--
[oc_codingCovBridge_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean)
-/
@[path]
private lemma oc_codingCovBridge_refl_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ} :
-- imply
  oc_CodingCovBridge (ν := ν) f (expect ν f) (∑ e, cov ν (CovLowerBound.coordI e) f) := by
-- proof
  apply StatMech.Walls.oc_codingCovBridge_refl f


-- created on 2026-10-23
