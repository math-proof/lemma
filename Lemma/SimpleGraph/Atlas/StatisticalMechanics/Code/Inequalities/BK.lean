import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
open MeasureTheory Finset StatMech


/--
[pweight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma pweight_nonneg_eq
  [Fintype E]
  {φ : E → Bool → ℝ}
  {ω : ConfigSpace E}
-- given
  (hφ : ∀ x b, 0 ≤ φ x b) :
-- imply
  0 ≤ pweight φ ω := by
-- proof
  apply StatMech.pweight_nonneg hφ ω

/--
[wprob_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma wprob_mono_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {S T : Set (ConfigSpace E)}
-- given
  (hφ : ∀ x b, 0 ≤ φ x b)
  (h : S ⊆ T) :
-- imply
  wprob φ S ≤ wprob φ T := by
-- proof
  apply StatMech.wprob_mono hφ h

/--
[wprob_union_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma wprob_union_inter_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {U V : Set (ConfigSpace E)} :
-- imply
  wprob φ (U ∪ V) + wprob φ (U ∩ V) = wprob φ U + wprob φ V := by
-- proof
  apply StatMech.wprob_union_inter φ U V

/--
[bk_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma bk_algebra_eq
  {a0 a1 b0 b1 p q c0 c1 m : ℝ}
-- given
  (hq : q = 1 - p)
  (hp0 : 0 ≤ p)
  (hq0 : 0 ≤ q)
  (hmab : m ≤ a0 * b0)
  (hc0m : c0 ≤ m)
  (hc1u : c1 ≤ a0 * b1 + a1 * b0 - m)
  (hc1v : c1 ≤ a1 * b1) :
-- imply
  q * c0 + p * c1 ≤ (q * a0 + p * a1) * (q * b0 + p * b1) := by
-- proof
  apply StatMech.bk_algebra a0 a1 b0 b1 p q c0 c1 m hq hp0 hq0 hmab hc0m hc1u hc1v

/--
[indicator_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma indicator_slice_eq
  {n : ℕ}
  {S : Set (ConfigSpace (Fin (n + 1)))}
  {x : Bool}
  {ω' : ConfigSpace (Fin n)} :
-- imply
  S.indicator (fun _ => (1 : ℝ)) (Fin.cons x ω') = (slice S x).indicator (fun _ => (1 : ℝ)) ω' := by
-- proof
  apply StatMech.indicator_slice S x ω'

/--
[pweight_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma pweight_cons_eq
  {n : ℕ}
  {φ : Fin (n + 1) → Bool → ℝ}
  {x : Bool}
  {ω' : ConfigSpace (Fin n)} :
-- imply
  pweight φ (Fin.cons x ω') = φ 0 x * pweight (fun j => φ j.succ) ω' := by
-- proof
  apply StatMech.pweight_cons φ x ω'

/--
[wprob_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma wprob_slice_eq
  {n : ℕ}
  {φ : Fin (n + 1) → Bool → ℝ}
  {S : Set (ConfigSpace (Fin (n + 1)))} :
-- imply
  wprob φ S = φ 0 false * wprob (fun j => φ j.succ) (slice S false) + φ 0 true * wprob (fun j => φ j.succ) (slice S true) := by
-- proof
  apply StatMech.wprob_slice φ S

/--
[slice_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma slice_isIncreasing_eq
  {n : ℕ}
  {C : Set (ConfigSpace (Fin (n + 1)))}
  {x : Bool}
-- given
  (hC : IsIncreasing C) :
-- imply
  IsIncreasing (slice C x) := by
-- proof
  apply StatMech.slice_isIncreasing hC x

/--
[slice_false_subset_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma slice_false_subset_true_eq
  {n : ℕ}
  {C : Set (ConfigSpace (Fin (n + 1)))}
-- given
  (hC : IsIncreasing C) :
-- imply
  slice C false ⊆ slice C true := by
-- proof
  apply StatMech.slice_false_subset_true hC

/--
[occursOn_slice_of_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma occursOn_slice_of_false_eq
  {n : ℕ}
  {C : Set (ConfigSpace (Fin (n + 1)))}
  {K : Set (Fin (n + 1))}
  {ω' : ConfigSpace (Fin n)}
-- given
  (h : OccursOn C K (Fin.cons false ω')) :
-- imply
  OccursOn (slice C false) (sliceSet K) ω' := by
-- proof
  apply StatMech.occursOn_slice_of_false h

/--
[occursOn_slice_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma occursOn_slice_true_eq
  {n : ℕ}
  {C : Set (ConfigSpace (Fin (n + 1)))}
  {K : Set (Fin (n + 1))}
  {ω' : ConfigSpace (Fin n)}
-- given
  (h : OccursOn C K (Fin.cons true ω')) :
-- imply
  OccursOn (slice C true) (sliceSet K) ω' := by
-- proof
  apply StatMech.occursOn_slice_true h

/--
[occursOn_slice_false_notmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma occursOn_slice_false_notmem_eq
  {n : ℕ}
  {C : Set (ConfigSpace (Fin (n + 1)))}
  {K : Set (Fin (n + 1))}
  {x : Bool}
  {ω' : ConfigSpace (Fin n)}
-- given
  (h0 : (0 : Fin (n + 1)) ∉ K)
  (h : OccursOn C K (Fin.cons x ω')) :
-- imply
  OccursOn (slice C false) (sliceSet K) ω' := by
-- proof
  apply StatMech.occursOn_slice_false_notmem h0 h

/--
[sliceSet_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma sliceSet_disjoint_eq
  {n : ℕ}
  {K L : Set (Fin (n + 1))}
-- given
  (h : Disjoint K L) :
-- imply
  Disjoint (sliceSet K) (sliceSet L) := by
-- proof
  apply StatMech.sliceSet_disjoint h

/--
[slice_disjointOccurrence_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma slice_disjointOccurrence_false_eq
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin (n + 1)))} :
-- imply
  slice (disjointOccurrence A B) false ⊆ disjointOccurrence (slice A false) (slice B false) := by
-- proof
  apply StatMech.slice_disjointOccurrence_false

/--
[slice_disjointOccurrence_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma slice_disjointOccurrence_true_eq
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin (n + 1)))} :
-- imply
  slice (disjointOccurrence A B) true ⊆ disjointOccurrence (slice A false) (slice B true) ∪ disjointOccurrence (slice A true) (slice B false) := by
-- proof
  apply StatMech.slice_disjointOccurrence_true

/--
[occursOn_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma occursOn_subsingleton_eq
  {n : ℕ}
  [Subsingleton (ConfigSpace (Fin n))]
  {A : Set (ConfigSpace (Fin n))}
  {K : Set (Fin n)}
  {ω : ConfigSpace (Fin n)} :
-- imply
  OccursOn A K ω ↔ ω ∈ A := by
-- proof
  apply StatMech.occursOn_subsingleton

/--
[disjointOccurrence_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma disjointOccurrence_subsingleton_eq
  {n : ℕ}
  [Subsingleton (ConfigSpace (Fin n))]
  {A B : Set (ConfigSpace (Fin n))} :
-- imply
  disjointOccurrence A B = A ∩ B := by
-- proof
  apply StatMech.disjointOccurrence_subsingleton A B

/--
[bk_wprob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma bk_wprob_eq :
-- imply
  ∀ (n : ℕ) (φ : Fin n → Bool → ℝ), (∀ i b, 0 ≤ φ i b) → (∀ i, φ i false + φ i true = 1) → ∀ (A B : Set (ConfigSpace (Fin n))), IsIncreasing A → IsIncreasing B → wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.bk_wprob

/--
[cfgEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma cfgEquiv_apply_eq
  {e : E ≃ F}
  {ω : ConfigSpace F}
  {x : E} :
-- imply
  cfgEquiv e ω x = ω (e x) := by
-- proof
  apply StatMech.cfgEquiv_apply e ω x

/--
[cfgEquiv_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma cfgEquiv_mono_eq
  {e : E ≃ F}
  {ω ω' : ConfigSpace F}
-- given
  (h : ω ≤ ω') :
-- imply
  cfgEquiv e ω ≤ cfgEquiv e ω' := by
-- proof
  apply StatMech.cfgEquiv_mono e h

/--
[isIncreasing_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma isIncreasing_preimage_eq
  {e : E ≃ F}
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing ((cfgEquiv e) ⁻¹' A) := by
-- proof
  apply StatMech.isIncreasing_preimage e hA

/--
[agreeOn_cfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma agreeOn_cfgEquiv_eq
  {e : E ≃ F}
  {K : Set E}
  {ωf ωf' : ConfigSpace F} :
-- imply
  agreeOn (e '' K) ωf ωf' ↔ agreeOn K (cfgEquiv e ωf) (cfgEquiv e ωf') := by
-- proof
  apply StatMech.agreeOn_cfgEquiv e K ωf ωf'

/--
[occursOn_cfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma occursOn_cfgEquiv_eq
  {e : E ≃ F}
  {A : Set (ConfigSpace E)}
  {K : Set E}
  {ωf : ConfigSpace F} :
-- imply
  OccursOn ((cfgEquiv e) ⁻¹' A) (e '' K) ωf ↔ OccursOn A K (cfgEquiv e ωf) := by
-- proof
  apply StatMech.occursOn_cfgEquiv e A K ωf

/--
[preimage_disjointOccurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma preimage_disjointOccurrence_eq
  {e : E ≃ F}
  {A B : Set (ConfigSpace E)} :
-- imply
  (cfgEquiv e) ⁻¹' (disjointOccurrence A B) = disjointOccurrence ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B) := by
-- proof
  apply StatMech.preimage_disjointOccurrence e A B

/--
[pweight_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma pweight_transfer_eq
  [Fintype E]
  [Fintype F]
  {e : E ≃ F}
  {φ : E → Bool → ℝ}
  {ωf : ConfigSpace F} :
-- imply
  pweight φ (cfgEquiv e ωf) = pweight (fun y => φ (e.symm y)) ωf := by
-- proof
  apply StatMech.pweight_transfer e φ ωf

/--
[wprob_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma wprob_transfer_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  {e : E ≃ F}
  {φ : E → Bool → ℝ}
  {S : Set (ConfigSpace E)} :
-- imply
  wprob φ S = wprob (fun y => φ (e.symm y)) ((cfgEquiv e) ⁻¹' S) := by
-- proof
  apply StatMech.wprob_transfer e φ S

/--
[bk_wprob_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma bk_wprob_general_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.bk_wprob_general φ hφ0 hφ1 hA hB

/--
[bernoulli_real_eq_wprob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma bernoulli_real_eq_wprob_eq
  [Fintype E]
  [DecidableEq E]
  {p : NNReal}
  {S : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real S = wprob (fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b}) S := by
-- proof
  apply StatMech.bernoulli_real_eq_wprob hp S

/--
[bk_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean)
-/
@[path]
private lemma bk_inequality_eq
  [Fintype E]
  [DecidableEq E]
  {p : NNReal}
  {A B : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.bk_inequality hp hA hB


-- created on 2026-10-23
