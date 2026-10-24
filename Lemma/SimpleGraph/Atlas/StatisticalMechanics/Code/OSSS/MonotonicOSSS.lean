import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.MonotonicOSSS
open Finset MeasureTheory Set StatMech StatMech.OSSS StatMech.OSSS.MonotonicFK StatMech.OSSS.MonotonicMeasure


/--
[fkMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma fkMass_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < fkMass G p q ω := by
-- proof
  apply StatMech.OSSS.MonotonicFK.fkMass_pos G hp hp1 hq ω

/--
[fkMass_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma fkMass_sum_eq_one_eq
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
  ∑ ω : ConfigSpace (Sym2 V), fkMass G p q ω = 1 := by
-- proof
  apply StatMech.OSSS.MonotonicFK.fkMass_sum_eq_one G hp hp1 hq

/--
[fk_codeProb_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma fk_codeProb_eq_mass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {x : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∏ t : Fin n, Coding.condProbBit (fkMass G p q) (Coding.prefixSet (σ : Fin n → Sym2 V) (t : ℕ)) x ((σ : Fin n → Sym2 V) t) (x ((σ : Fin n → Sym2 V) t))) = fkMass G p q x := by
-- proof
  apply StatMech.OSSS.MonotonicFK.fk_codeProb_eq_mass G hp hp1 hq σ x

/--
[fk_volume_codeFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma fk_volume_codeFibre_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {x : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (volume (Coding.codeFibre (fkMass G p q) σ x)).toReal = fkMass G p q x := by
-- proof
  apply StatMech.OSSS.MonotonicFK.fk_volume_codeFibre G hp hp1 hq σ x

/--
[fkMass_isMonotonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma fkMass_isMonotonic_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Monotonic.IsMonotonicMeasure (fkMass G p q) := by
-- proof
  apply StatMech.OSSS.MonotonicFK.fkMass_isMonotonic G hp hp1 hq

/--
[genMean_fkMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma genMean_fkMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  genMean (fkMass G p q) g = FK.fkMean G p q g := by
-- proof
  apply StatMech.OSSS.MonotonicFK.genMean_fkMass G p q g

/--
[genCov_fkMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma genCov_fkMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  genCov (fkMass G p q) f g = FK.fkCov G p q f g := by
-- proof
  apply StatMech.OSSS.MonotonicFK.genCov_fkMass G p q f g

/--
[genCoord_eq_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma genCoord_eq_coord_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : Sym2 V} :
-- imply
  (genCoord e : ConfigSpace (Sym2 V) → ℝ) = FK.coord e := by
-- proof
  apply StatMech.OSSS.MonotonicFK.genCoord_eq_coord G e

/--
[genVar_fkMass_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma genVar_fkMass_indicator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))} :
-- imply
  genVar (fkMass G p q) (A.indicator (fun _ => (1 : ℝ))) = FK.fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.OSSS.MonotonicFK.genVar_fkMass_indicator G p q A

/--
[fkVar_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma fkVar_indicator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))} :
-- imply
  genVar (fkMass G p q) (A.indicator (fun _ => (1 : ℝ))) = FK.fkProbOf G p q A * (1 - FK.fkProbOf G p q A) := by
-- proof
  apply StatMech.OSSS.MonotonicFK.fkVar_indicator G p q A

/--
[monotonicOSSS_to_fkCov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma monotonicOSSS_to_fkCov_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
  {N : ℕ}
  {c₀ D : ℝ}
-- given
  (hMonOSSS : MonotonicOSSSBound (fkMass G p 2) G.edgeFinset (A.indicator (fun _ => (1 : ℝ))) N c₀ D) :
-- imply
  (N : ℝ) * c₀ * (FK.fkProbOf G p 2 A * (1 - FK.fkProbOf G p 2 A)) ≤ D * ∑ e ∈ G.edgeFinset, FK.fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
-- proof
  apply StatMech.OSSS.MonotonicFK.monotonicOSSS_to_fkCov G p A N c₀ D hMonOSSS

/--
[genMean_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma genMean_weight_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  genMean (weight ν) g = expect ν g := by
-- proof
  apply StatMech.OSSS.MonotonicMeasure.genMean_weight g

/--
[genCov_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma genCov_weight_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {f g : ConfigSpace E → ℝ} :
-- imply
  genCov (weight ν) f g = cov ν f g := by
-- proof
  apply StatMech.OSSS.MonotonicMeasure.genCov_weight f g

/--
[genVar_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma genVar_weight_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  genVar (weight ν) g = var ν g := by
-- proof
  apply StatMech.OSSS.MonotonicMeasure.genVar_weight g

/--
[genCoord_eq_coordI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma genCoord_eq_coordI_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E} :
-- imply
  (genCoord e : ConfigSpace E → ℝ) = coordI e := by
-- proof
  apply StatMech.OSSS.MonotonicMeasure.genCoord_eq_coordI e

/--
[monotonicOSSSBound_of_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean)
-/
@[path]
private lemma monotonicOSSSBound_of_product_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {A : Set (ConfigSpace E)}
  {f : ConfigSpace E → ℝ}
  {T : κ → DecisionTree E}
  {R : κ → E → ℝ}
  {c₀ : ℝ}
  {D : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hf : f = A.indicator (fun _ => (1 : ℝ)))
  (hT : ∀ k, (T k).evalR = f)
  (hR : ∀ k e, reveal ν (T k) e ≤ R k e)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDnn : 0 ≤ D)
  (hD : ∀ e, (∑ k, R k e) ≤ D) :
-- imply
  MonotonicOSSSBound (weight ν) Finset.univ f (Fintype.card κ) c₀ D := by
-- proof
  apply StatMech.OSSS.MonotonicMeasure.monotonicOSSSBound_of_product hν hA hf T hT R hR c₀ hc₀nn hc₀ D hDnn hD


-- created on 2026-10-23
