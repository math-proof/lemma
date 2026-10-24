import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.FKSharpnessUncond
open Finset Real Set StatMech.Lattice StatMech StatMech.OSSS


/--
[cov_crossbox_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessUncond.lean)
-/
@[path]
private lemma cov_crossbox_uncond_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {n : ℕ}
  {ν : E → Bool → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {l : List E}
  {disc₀ : ℕ → Finset (Site d)}
  {Λ : Finset (Site d)}
  {μ : Site d → ℕ → ℝ}
  {ru rv : E → ℕ}
  {c₀ : ℝ}
-- given
  (hn : 1 ≤ n)
  (hν : IsProbWeight ν)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
  (hl : ∀ e, e ∈ l)
  (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
  (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
  (hoB : ∀ k, o ∉ disc₀ k)
  (hΛne : Λ.Nonempty)
  (hμ : ∀ x j, 0 ≤ μ x j)
  (hru : ∀ e, ru e ≤ n)
  (hrv : ∀ e, rv e ≤ n)
  (hΛu : ∀ e, endU e ∈ Λ)
  (hΛv : ∀ e, endV e ∈ Λ)
  (hcompu : ∀ e k, expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μ (endU e) ((k : ℤ) - (ru e : ℤ)).natAbs)
  (hcompv : ∀ e k, expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μ (endV e) ((k : ℤ) - (rv e : ℤ)).natAbs)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false) :
-- imply
  (n : ℝ) * c₀ * (expect ν ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) * (1 - expect ν ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))))) ≤ (4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j)) * ∑ e, cov ν (coordI e) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.OSSS.cov_crossbox_uncond hn hν hinj hcoh hadj o ho l hl disc₀ hdisc₀sub hdisc₀sup hoB Λ hΛne μ hμ ru rv hru hrv hΛu hΛv hcompu hcompv c₀ hc₀nn hc₀

/--
[osss_differential_inequality_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessUncond.lean)
-/
@[path]
private lemma osss_differential_inequality_uncond_eq
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
  apply StatMech.OSSS.osss_differential_inequality_uncond n c₀ cR D θ θ' S hD hcR hcov hRussoEq

/--
[theta_mul_one_sub_ge_of_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessUncond.lean)
-/
@[path]
private lemma theta_mul_one_sub_ge_of_bounded_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {θ κ : ℝ}
-- given
  (hθnn : 0 ≤ θ)
  (hθub : θ ≤ 1 - κ) :
-- imply
  θ * κ ≤ θ * (1 - θ) := by
-- proof
  apply StatMech.OSSS.theta_mul_one_sub_ge_of_bounded hθnn hθub

/--
[osss_subcritical_decay_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessUncond.lean)
-/
@[path]
private lemma osss_subcritical_decay_uncond_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {n : ℕ}
  {c₀ cR D κ : ℝ}
  {a b : ℝ}
  {θn θn' S : ℝ → ℝ}
-- given
  (hab : a < b)
  (hD : 0 < D)
  (hcR : 0 < cR)
  (hc₀ : 0 < c₀)
  (hn : 1 ≤ n)
  (hκ : 0 < κ)
  (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
  (hcov : ∀ x ∈ Icc a b, (n : ℝ) * c₀ * (θn x * (1 - θn x)) ≤ D * S x)
  (hRusso : ∀ x ∈ Icc a b, θn' x = cR * S x)
  (hθnn : ∀ x ∈ Icc a b, 0 ≤ θn x)
  (hθub : ∀ x ∈ Icc a b, θn x ≤ 1 - κ)
  (hθa : 0 ≤ θn a)
  (hθb : θn b ≤ 1) :
-- imply
  θn a ≤ Real.exp (-((n : ℝ) * c₀ * cR / D * κ * (b - a))) := by
-- proof
  apply StatMech.OSSS.osss_subcritical_decay_uncond n c₀ cR D κ a b hab hD hcR hc₀ hn hκ θn θn' S hd hcov hRusso hθnn hθub hθa hθb

/--
[osss_crossing_decay_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessUncond.lean)
-/
@[path]
private lemma osss_crossing_decay_uncond_eq
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
  {ru rv : E → ℕ}
  {ν : ℝ → E → Bool → ℝ}
  {μ : ℝ → Site d → ℕ → ℝ}
  {c₀ : ℝ}
  {cR κ : ℝ}
  {a b : ℝ}
  {Dval : ℝ}
  {θn' S : ℝ → ℝ}
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
  (hru : ∀ e, ru e ≤ n)
  (hrv : ∀ e, rv e ≤ n)
  (hΛu : ∀ e, endU e ∈ Λ)
  (hΛv : ∀ e, endV e ∈ Λ)
  (hν : ∀ x, IsProbWeight (ν x))
  (hμ : ∀ x p j, 0 ≤ μ x p j)
  (hcompu : ∀ x e k, expect (ν x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μ x (endU e) ((k : ℤ) - (ru e : ℤ)).natAbs)
  (hcompv : ∀ x e k, expect (ν x) (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ μ x (endV e) ((k : ℤ) - (rv e : ℤ)).natAbs)
  (hc₀ : 0 < c₀)
  (hc₀le : ∀ x e, c₀ ≤ ν x e true * ν x e false)
  (hab : a < b)
  (hcR : 0 < cR)
  (hκ : 0 < κ)
  (hDpos : 0 < Dval)
  (hDeq : ∀ x ∈ Icc a b, Dval = 4 * Λ.sup' hΛne (fun y => ∑ j ∈ Finset.range (n + 1), μ x y j))
  (hd : ∀ x ∈ Icc a b, HasDerivAt (fun x => expect (ν x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ)))) (θn' x) x)
  (hScov : ∀ x ∈ Icc a b, S x = ∑ e, cov (ν x) (coordI e) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))))
  (hRusso : ∀ x ∈ Icc a b, θn' x = cR * S x)
  (hθnn : ∀ x ∈ Icc a b, 0 ≤ expect (ν x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))))
  (hθub : ∀ x ∈ Icc a b, expect (ν x) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ 1 - κ)
  (hθa : 0 ≤ expect (ν a) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))))
  (hθb : expect (ν b) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ 1) :
-- imply
  expect (ν a) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) ≤ Real.exp (-((n : ℝ) * c₀ * cR / Dval * κ * (b - a))) := by
-- proof
  apply StatMech.OSSS.osss_crossing_decay_uncond hn hinj hcoh hadj o ho l hl disc₀ hdisc₀sub hdisc₀sup hoB Λ hΛne ru rv hru hrv hΛu hΛv ν hν μ hμ hcompu hcompv c₀ hc₀ hc₀le cR κ a b hab hcR hκ Dval hDpos hDeq θn' S hd hScov hRusso hθnn hθub hθa hθb


-- created on 2026-10-23
