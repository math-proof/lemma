import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruct
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[tfx_htrif_of_mergeFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruct.lean)
-/
@[path]
private lemma tfx_htrif_of_mergeFree_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hmf : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))), ω ∈ threeMeetBox d n → bka_MergeFree ω) :
-- imply
  0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsTrifurcation d ω 0} := by
-- proof
  apply StatMech.Percolation.tfx_htrif_of_mergeFree μ hfe hmf

/--
[bkc_htrif_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruct.lean)
-/
@[path]
private lemma bkc_htrif_bernoulli_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hmf : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))), ω ∈ threeMeetBox d n → bka_MergeFree ω) :
-- imply
  0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0} := by
-- proof
  apply StatMech.Percolation.bkc_htrif_bernoulli p hp1 hp0 hmf

/--
[tfx_burton_keane_bernoulli_of_mergeFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruct.lean)
-/
@[path]
private lemma tfx_burton_keane_bernoulli_of_mergeFree_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ boxSV_boundaryCard d n)
  (hmf : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))), ω ∈ threeMeetBox d n → bka_MergeFree ω) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.tfx_burton_keane_bernoulli_of_mergeFree hd p hp1 hp0 hbound hmf


-- created on 2026-10-23
