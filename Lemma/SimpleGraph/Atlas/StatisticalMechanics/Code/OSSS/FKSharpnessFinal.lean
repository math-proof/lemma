import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.FKSharpnessFinal
open Finset Real Set StatMech.Lattice StatMech StatMech.OSSS


/--
[expect_bernoulliWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessFinal.lean)
-/
@[path]
private lemma expect_bernoulliWeight_eq
  [Fintype E]
  [DecidableEq E]
  {x : ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  expect (bernoulliWeight (E := E) x) g = StatMech.BeffaraDC.expect x g := by
-- proof
  apply StatMech.OSSS.expect_bernoulliWeight x g

/--
[expect_indicator_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessFinal.lean)
-/
@[path]
private lemma expect_indicator_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {x : ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  expect (bernoulliWeight (E := E) x) (A.indicator (fun _ => (1 : ℝ))) = StatMech.prob x A := by
-- proof
  apply StatMech.OSSS.expect_indicator_bernoulli x A

/--
[coordI_eq_openEdge_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessFinal.lean)
-/
@[path]
private lemma coordI_eq_openEdge_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {e : E} :
-- imply
  coordI (E := E) e = (StatMech.BeffaraDC.openEdge e).indicator (fun _ => (1 : ℝ)) := by
-- proof
  apply StatMech.OSSS.coordI_eq_openEdge_indicator e

/--
[cov_coordI_indicator_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessFinal.lean)
-/
@[path]
private lemma cov_coordI_indicator_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {x : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E} :
-- imply
  cov (bernoulliWeight (E := E) x) (coordI e) (A.indicator (fun _ => (1 : ℝ))) = StatMech.prob x (A ∩ StatMech.BeffaraDC.openEdge e) - StatMech.prob x (StatMech.BeffaraDC.openEdge e) * StatMech.prob x A := by
-- proof
  apply StatMech.OSSS.cov_coordI_indicator_bernoulli x A e

/--
[hasDerivAt_crossing_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessFinal.lean)
-/
@[path]
private lemma hasDerivAt_crossing_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {x : ℝ}
-- given
  (hA : IsIncreasing A)
  (hx0 : x ≠ 0)
  (hx1 : x ≠ 1) :
-- imply
  HasDerivAt (fun x => expect (bernoulliWeight (E := E) x) (A.indicator (fun _ => (1 : ℝ)))) ((1 / (x * (1 - x))) * ∑ e, cov (bernoulliWeight (E := E) x) (coordI e) (A.indicator (fun _ => (1 : ℝ)))) x := by
-- proof
  apply StatMech.OSSS.hasDerivAt_crossing_bernoulli A hA hx0 hx1

/--
[expect_indicator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessFinal.lean)
-/
@[path]
private lemma expect_indicator_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ expect ν (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.OSSS.expect_indicator_nonneg hν A

/--
[expect_indicator_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessFinal.lean)
-/
@[path]
private lemma expect_indicator_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hν : IsProbWeight ν) :
-- imply
  expect ν (A.indicator (fun _ => (1 : ℝ))) ≤ 1 := by
-- proof
  apply StatMech.OSSS.expect_indicator_le_one hν A

/--
[pointwise_di_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessFinal.lean)
-/
@[path]
private lemma pointwise_di_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {n : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {l : List E}
  {disc₀ : ℕ → Finset (Site d)}
  {Λ : Finset (Site d)}
  {μ : Site d → ℕ → ℝ}
  {ru rv : E → ℕ}
  {Dval : ℝ}
  {x : ℝ}
  {κ : ℝ}
-- given
  (hn : 1 ≤ n)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
  (hl : ∀ e, e ∈ l)
  (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
  (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
  (hoB : ∀ k, o ∉ disc₀ k)
  (hΛne : Λ.Nonempty)
  (hμ : ∀ y j, 0 ≤ μ y j)
  (hru : ∀ e, ru e ≤ n)
  (hrv : ∀ e, rv e ≤ n)
  (hΛu : ∀ e, endU e ∈ Λ)
  (hΛv : ∀ e, endV e ∈ Λ)
  (hDpos : 0 < Dval)
  (hDeq : Dval = 4 * Λ.sup' hΛne (fun y => ∑ j ∈ Finset.range (n + 1), μ y j))
  (hx0 : 0 < x)
  (hx1 : x < 1)
  (hcompu : ∀ e k, expect (bernoulliWeight (E := E) x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μ (endU e) ((k : ℤ) - (ru e : ℤ)).natAbs)
  (hcompv : ∀ e k, expect (bernoulliWeight (E := E) x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μ (endV e) ((k : ℤ) - (rv e : ℤ)).natAbs)
  (hθub : expect (bernoulliWeight (E := E) x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ 1 - κ) :
-- imply
  (n : ℝ) * κ / Dval * expect (bernoulliWeight (E := E) x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ (1 / (x * (1 - x))) * ∑ e, cov (bernoulliWeight (E := E) x) (coordI e) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.OSSS.pointwise_di_bernoulli hn hinj hcoh hadj o ho l hl disc₀ hdisc₀sub hdisc₀sup hoB Λ hΛne μ hμ ru rv hru hrv hΛu hΛv Dval hDpos hDeq x hx0 hx1 hcompu hcompv κ hθub

/--
[osss_fk_sharpness_final](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessFinal.lean)
-/
@[path]
private lemma osss_fk_sharpness_final_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {n : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {l : List E}
  {disc₀ : ℕ → Finset (Site d)}
  {Λ : Finset (Site d)}
  {μ : Site d → ℕ → ℝ}
  {ru rv : E → ℕ}
  {Dval : ℝ}
  {κ : ℝ}
  {a b : ℝ}
-- given
  (hn : 1 ≤ n)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
  (hl : ∀ e, e ∈ l)
  (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
  (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
  (hoB : ∀ k, o ∉ disc₀ k)
  (hΛne : Λ.Nonempty)
  (hμ : ∀ y j, 0 ≤ μ y j)
  (hru : ∀ e, ru e ≤ n)
  (hrv : ∀ e, rv e ≤ n)
  (hΛu : ∀ e, endU e ∈ Λ)
  (hΛv : ∀ e, endV e ∈ Λ)
  (hDpos : 0 < Dval)
  (hDeq : Dval = 4 * Λ.sup' hΛne (fun y => ∑ j ∈ Finset.range (n + 1), μ y j))
  (hκ : 0 < κ)
  (hab : a < b)
  (ha0 : 0 < a)
  (hb1 : b < 1)
  (hcompu : ∀ x ∈ Icc a b, ∀ e k, expect (bernoulliWeight (E := E) x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μ (endU e) ((k : ℤ) - (ru e : ℤ)).natAbs)
  (hcompv : ∀ x ∈ Icc a b, ∀ e k, expect (bernoulliWeight (E := E) x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μ (endV e) ((k : ℤ) - (rv e : ℤ)).natAbs)
  (hθub : ∀ x ∈ Icc a b, expect (bernoulliWeight (E := E) x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ 1 - κ) :
-- imply
  expect (bernoulliWeight (E := E) a) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ Real.exp (-((n : ℝ) * κ / Dval * (b - a))) := by
-- proof
  apply StatMech.OSSS.osss_fk_sharpness_final hn hinj hcoh hadj o ho l hl disc₀ hdisc₀sub hdisc₀sup hoB Λ hΛne μ hμ ru rv hru hrv hΛu hΛv Dval hDpos hDeq κ hκ a b hab ha0 hb1 hcompu hcompv hθub


-- created on 2026-10-23
