import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BKFirstExit
open MeasureTheory Finset Set StatMech StatMech.Sharpness


/--
[susceptibility_self_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BKFirstExit.lean)
-/
@[path]
private lemma susceptibility_self_consistent_eq
  [DecidableEq ι]
  {Lam S : Finset ι}
  {bnd : Finset κ}
  {outer : κ → ι}
  {p : ℝ}
  {cw : κ → ℝ}
  {q : ι → ℝ}
  {q' : ι → ι → ℝ}
  {χ : ℝ}
  {φ : ℝ}
-- given
  (hSΛ : S ⊆ Lam)
  (hp0 : 0 ≤ p)
  (hq'_nonneg : ∀ b x, 0 ≤ q' b x)
  (hcw_nonneg : ∀ e, 0 ≤ cw e)
  (hq_le_one : ∀ x ∈ S, q x ≤ 1)
  (hfe : ∀ x ∈ Lam, x ∉ S → q x ≤ ∑ e ∈ bnd, (p * cw e) * q' (outer e) x)
  (hχ : χ = ∑ x ∈ Lam, q x)
  (hcont : ∀ b, ∑ x ∈ Lam, q' b x ≤ χ)
  (hφ : φ = p * ∑ e ∈ bnd, cw e) :
-- imply
  χ ≤ (S.card : ℝ) + φ * χ := by
-- proof
  apply StatMech.Sharpness.susceptibility_self_consistent Lam S hSΛ bnd outer p hp0 cw q q' hq'_nonneg hcw_nonneg hq_le_one hfe χ hχ hcont φ hφ

/--
[firstExit_target_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BKFirstExit.lean)
-/
@[path]
private lemma firstExit_target_bound_eq
  [Fintype V]
  [DecidableEq V]
  {p : NNReal}
  {G : SimpleGraph V}
  {Lam S : Set V}
  {u x : V}
  {s : Finset ι}
  {bp : ι → V × V}
-- given
  (hp : p ≤ 1)
  (hincl : connEvent G Lam u {x} ⊆ ⋃ i ∈ s, disjointOccurrence (connEvent G S u {(bp i).1}) (disjointOccurrence (edgeOpenEvent (bp i).1 (bp i).2) (connEvent G Lam (bp i).2 {x})))
  (hedge : ∀ i ∈ s, (bernoulliProductMeasure (E := Sym2 V) p hp).real (edgeOpenEvent (bp i).1 (bp i).2) ≤ (p : ℝ)) :
-- imply
  (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G Lam u {x}) ≤ ∑ i ∈ s, ((p : ℝ) * (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G S u {(bp i).1})) * (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G Lam (bp i).2 {x}) := by
-- proof
  apply StatMech.Sharpness.firstExit_target_bound hp G Lam S u x s bp hincl hedge

/--
[susceptibility_self_consistent_bk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BKFirstExit.lean)
-/
@[path]
private lemma susceptibility_self_consistent_bk_eq
  [Fintype V]
  [DecidableEq V]
  {p : NNReal}
  {G : SimpleGraph V}
  {Lam S : Finset V}
  {u : V}
  {bnd : Finset κ}
  {bp : κ → V × V}
  {χ : ℝ}
  {φ : ℝ}
-- given
  (hp : p ≤ 1)
  (hSΛ : S ⊆ Lam)
  (hincl : ∀ x ∈ Lam, x ∉ S → connEvent G (Lam : Set V) u {x} ⊆ ⋃ e ∈ bnd, disjointOccurrence (connEvent G (S : Set V) u {(bp e).1}) (disjointOccurrence (edgeOpenEvent (bp e).1 (bp e).2) (connEvent G (Lam : Set V) (bp e).2 {x})))
  (hedge : ∀ e ∈ bnd, (bernoulliProductMeasure (E := Sym2 V) p hp).real (edgeOpenEvent (bp e).1 (bp e).2) ≤ (p : ℝ))
  (hSone : ∀ x ∈ S, (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G (Lam : Set V) u {x}) ≤ 1)
  (hχ : χ = ∑ x ∈ Lam, (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G (Lam : Set V) u {x}))
  (hcont : ∀ b : V, ∑ x ∈ Lam, (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G (Lam : Set V) b {x}) ≤ χ)
  (hφ : φ = (p : ℝ) * ∑ e ∈ bnd, (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G (S : Set V) u {(bp e).1})) :
-- imply
  χ ≤ (S.card : ℝ) + φ * χ := by
-- proof
  apply StatMech.Sharpness.susceptibility_self_consistent_bk hp G Lam S hSΛ u bnd bp hincl hedge hSone χ hχ hcont φ hφ

/--
[susceptibility_finite_of_self_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BKFirstExit.lean)
-/
@[path]
private lemma susceptibility_finite_of_self_consistent_eq
  {chi Sval phival : ℝ}
-- given
  (hchi : 0 ≤ chi)
  (hphi1 : phival < 1)
  (hself : chi ≤ Sval + phival * chi) :
-- imply
  0 ≤ chi ∧ chi ≤ Sval / (1 - phival) := by
-- proof
  apply StatMech.Sharpness.susceptibility_finite_of_self_consistent chi Sval phival hchi hphi1 hself


-- created on 2026-10-23
