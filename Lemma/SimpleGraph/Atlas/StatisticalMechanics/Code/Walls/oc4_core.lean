import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc4_core
open MeasureTheory Finset Real Filter Topology Set StatMech StatMech.Walls


/--
[oc4_fk_hcov_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_core.lean)
-/
@[path]
private lemma oc4_fk_hcov_codingFrame_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  [Fintype κ]
  [Nonempty κ]
  {m : ℕ}
  {σf : κ → (Fin m ≃ Sym2 V)}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {R : κ → Sym2 V → ℝ}
  {D : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hidem : ∀ ω, f ω * f ω = f ω)
  (hDpos : 0 < D)
  (hreach : ∀ k e, revealAdapt (fkMass G p 2) (σf k) f e ≤ R k e)
  (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
-- imply
  ((Fintype.card κ : ℝ) / (4 * ((Fintype.card κ : ℝ) * D / 4))) * (Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f)) ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.Walls.oc4_fk_hcov_codingFrame G hp hp1 σf hf hf0 hf1 hidem R D hDpos hreach hsum

/--
[oc4_fk_reveal_input_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_core.lean)
-/
@[path]
private lemma oc4_fk_reveal_input_codingFrame_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  revealAdapt (fkMass G p q) σ f e = reachProb (fkMass G p q) σ f e ∧ reachProb (fkMass G p q) σ f e = oc4_notDetProb (fkMass G p q) σ f e := by
-- proof
  apply StatMech.Walls.oc4_fk_reveal_input_codingFrame G hp hp1 hq σ f e

/--
[oc4_fk_hcovFamily_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_core.lean)
-/
@[path]
private lemma oc4_fk_hcovFamily_codingFrame_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {pf : ℕ → ℝ → ℝ}
  {ff : ℕ → ℝ → ConfigSpace (Sym2 V) → ℝ}
  {κ : ℕ → Type}
  [∀ n, Fintype (κ n)]
  [∀ n, Nonempty (κ n)]
  {mdim : ℕ → ℕ}
  {Dseq : ℕ → ℝ → ℝ}
  {β δ : ℝ}
-- given
  (σf : ∀ n, κ n → (Fin (mdim n) ≃ Sym2 V))
  (Rfam : ∀ n, κ n → Sym2 V → ℝ)
  (hp : ∀ n x, x ∈ Icc (β - 2 * δ) β → 0 < pf n x)
  (hp1 : ∀ n x, x ∈ Icc (β - 2 * δ) β → pf n x < 1)
  (hfmono : ∀ n x, Monotone (ff n x))
  (hf0 : ∀ n x, 0 ≤ ff n x)
  (hf1 : ∀ n x ω, ff n x ω ≤ 1)
  (hidem : ∀ n x ω, ff n x ω * ff n x ω = ff n x ω)
  (hDpos : ∀ n x, x ∈ Icc (β - 2 * δ) β → 0 < Dseq n x)
  (hreach : ∀ n x, x ∈ Icc (β - 2 * δ) β → ∀ k e, revealAdapt (fkMass (Gf n) (pf n x) 2) (σf n k) (ff n x) e ≤ Rfam n k e)
  (hsum : ∀ n x, x ∈ Icc (β - 2 * δ) β → ∀ e, (∑ k, Rfam n k e) ≤ (Fintype.card (κ n) : ℝ) * Dseq n x) :
-- imply
  ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x) * (1 - Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x)) / Dseq n x ≤ ∑ e, Lindeberg.cov (fkMass (Gf n) (pf n x) 2) (ff n x) (Lindeberg.coord e) := by
-- proof
  apply StatMech.Walls.oc4_fk_hcovFamily_codingFrame Gf pf ff mdim σf Rfam Dseq β δ hp hp1 hfmono hf0 hf1 hidem hDpos hreach hsum

/--
[oc4_fk_sharp_subcritical_of_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_core.lean)
-/
@[path]
private lemma oc4_fk_sharp_subcritical_of_codingFrame_eq
  [Fintype E]
  [Nonempty E]
  {θ θ' : ℕ → ℝ → ℝ}
  {J : E → ℝ}
  {Cov : ℕ → ℝ → E → ℝ}
  {cRf : ℕ → ℝ → ℝ}
  {Dseq : ℕ → ℝ → ℝ}
  {α δ β M : ℝ}
  {N : ℕ}
-- given
  (hδ : 0 < δ)
  (hα : 0 < α)
  (hα1 : α ≤ 1)
  (hMnn : 0 ≤ M)
  (hN : 1 ≤ N)
  (hJ : ∀ e, 0 < J e)
  (hxpos : ∀ x ∈ Icc (β - 2 * δ) β, 0 < x)
  (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
  (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
  (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
  (hθlt1 : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x < 1)
  (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β → y ≤ x → θ k y ≤ θ k x)
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
  (hDpos : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < Dseq n x)
  (hCovnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ∀ e, 0 ≤ Cov n x e)
  (hderiv : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ' n x = ∑ e, (J e / (Real.exp (x * J e) - 1)) * Cov n x e)
  (hcovGenuine : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x * (1 - θ n x) / Dseq n x ≤ ∑ e, Cov n x e)
  (hcRf : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < cRf n x ∧ ∀ e, cRf n x ≤ J e / (Real.exp (x * J e) - 1))
  (hident : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, Sig θ n x * (cRf n x * (1 - θ n x)) = 4 * ((n : ℝ) * Dseq n x / 4))
  (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α)) :
-- imply
  ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.Walls.oc4_fk_sharp_subcritical_of_codingFrame θ θ' J Cov cRf Dseq α δ β M N hδ hα hα1 hMnn hN hJ hxpos hd hθnn hθM hθlt1 hθmono hSpos hDpos hCovnn hderiv hcovGenuine hcRf hident hSpoly

/--
[oc4_fk_sharpness_of_codingFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_core.lean)
-/
@[path]
private lemma oc4_fk_sharpness_of_codingFrame_eq
  [Fintype E]
  [Nonempty E]
  {θ θ' : ℕ → ℝ → ℝ}
  {J : E → ℝ}
  {Cov : ℕ → ℝ → E → ℝ}
  {cRf : ℕ → ℝ → ℝ}
  {Dseq : ℕ → ℝ → ℝ}
  {α δ β M : ℝ}
  {N : ℕ}
  {T : ℕ → ℝ → ℝ}
  {mseq : ℕ → ℝ}
  {β₂' β₂ fβ₂ fβ₂' mlim : ℝ}
-- given
  (hδ : 0 < δ)
  (hα : 0 < α)
  (hα1 : α ≤ 1)
  (hMnn : 0 ≤ M)
  (hN : 1 ≤ N)
  (hJ : ∀ e, 0 < J e)
  (hxpos : ∀ x ∈ Icc (β - 2 * δ) β, 0 < x)
  (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (θ n) (θ' n x) x)
  (hθnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 ≤ θ n x)
  (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x ≤ M)
  (hθlt1 : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x < 1)
  (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β → y ≤ x → θ k y ≤ θ k x)
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig θ n x)
  (hDpos : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < Dseq n x)
  (hCovnn : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, ∀ e, 0 ≤ Cov n x e)
  (hderiv : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ' n x = ∑ e, (J e / (Real.exp (x * J e) - 1)) * Cov n x e)
  (hcovGenuine : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ n x * (1 - θ n x) / Dseq n x ≤ ∑ e, Cov n x e)
  (hcRf : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < cRf n x ∧ ∀ e, cRf n x ≤ J e / (Real.exp (x * J e) - 1))
  (hident : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, Sig θ n x * (cRf n x * (1 - θ n x)) = 4 * ((n : ℝ) * Dseq n x / 4))
  (hSpoly : ∀ n : ℕ, N ≤ n → Sig θ n β ≤ (n : ℝ) ^ (1 - α))
  (hββ : β₂' ≤ β₂)
  (hm1 : 1 ≤ mlim)
  (hTβ : Tendsto (fun n => T n β₂) atTop (𝓝 fβ₂))
  (hTβ' : Tendsto (fun n => T n β₂') atTop (𝓝 fβ₂'))
  (hmlim : Tendsto mseq atTop (𝓝 mlim))
  (hbound : ∀ᶠ n in atTop, (β₂ - β₂') * mseq n ≤ T n β₂ - T n β₂') :
-- imply
  (∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → θ n (β - 2 * δ) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ))) ∧ (β₂ - β₂' ≤ fβ₂ - fβ₂') := by
-- proof
  apply StatMech.Walls.oc4_fk_sharpness_of_codingFrame θ θ' J Cov cRf Dseq α δ β M N hδ hα hα1 hMnn hN hJ hxpos hd hθnn hθM hθlt1 hθmono hSpos hDpos hCovnn hderiv hcovGenuine hcRf hident hSpoly T mseq β₂' β₂ fβ₂ fβ₂' mlim hββ hm1 hTβ hTβ' hmlim hbound

/--
[oc4_fk_sharp_subcritical_fullyDischarged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_core.lean)
-/
@[path]
private lemma oc4_fk_sharp_subcritical_fullyDischarged_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty (Sym2 V)]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {pf : ℕ → ℝ → ℝ}
  {ff : ℕ → ℝ → ConfigSpace (Sym2 V) → ℝ}
  {κ : ℕ → Type}
  [∀ n, Fintype (κ n)]
  [∀ n, Nonempty (κ n)]
  {mdim : ℕ → ℕ}
  {Dseq : ℕ → ℝ → ℝ}
  {θ' : ℕ → ℝ → ℝ}
  {J : Sym2 V → ℝ}
  {cRf : ℕ → ℝ → ℝ}
  {α δ β M : ℝ}
  {N : ℕ}
-- given
  (σf : ∀ n, κ n → (Fin (mdim n) ≃ Sym2 V))
  (Rfam : ∀ n, κ n → Sym2 V → ℝ)
  (hδ : 0 < δ)
  (hα : 0 < α)
  (hα1 : α ≤ 1)
  (hMnn : 0 ≤ M)
  (hN : 1 ≤ N)
  (hJ : ∀ e, 0 < J e)
  (hxpos : ∀ x ∈ Icc (β - 2 * δ) β, 0 < x)
  (hp : ∀ n x, x ∈ Icc (β - 2 * δ) β → 0 < pf n x)
  (hp1 : ∀ n x, x ∈ Icc (β - 2 * δ) β → pf n x < 1)
  (hfmono : ∀ n x, Monotone (ff n x))
  (hf0 : ∀ n x, 0 ≤ ff n x)
  (hf1 : ∀ n x ω, ff n x ω ≤ 1)
  (hidem : ∀ n x ω, ff n x ω * ff n x ω = ff n x ω)
  (hDpos : ∀ n x, x ∈ Icc (β - 2 * δ) β → 0 < Dseq n x)
  (hreach : ∀ n x, x ∈ Icc (β - 2 * δ) β → ∀ k e, revealAdapt (fkMass (Gf n) (pf n x) 2) (σf n k) (ff n x) e ≤ Rfam n k e)
  (hsum : ∀ n x, x ∈ Icc (β - 2 * δ) β → ∀ e, (∑ k, Rfam n k e) ≤ (Fintype.card (κ n) : ℝ) * Dseq n x)
  (hd : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, HasDerivAt (fun y => Lindeberg.mean (fkMass (Gf n) (pf n y) 2) (ff n y)) (θ' n x) x)
  (hθM : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x) ≤ M)
  (hθlt1 : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x) < 1)
  (hθmono : ∀ k : ℕ, ∀ ⦃y x⦄, y ∈ Icc (β - 2 * δ) β → x ∈ Icc (β - 2 * δ) β → y ≤ x → Lindeberg.mean (fkMass (Gf k) (pf k y) 2) (ff k y) ≤ Lindeberg.mean (fkMass (Gf k) (pf k x) 2) (ff k x))
  (hSpos : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, 0 < Sig (fun n x => Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x)) n x)
  (hderiv : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, θ' n x = ∑ e, (J e / (Real.exp (x * J e) - 1)) * Lindeberg.cov (fkMass (Gf n) (pf n x) 2) (ff n x) (Lindeberg.coord e))
  (hcRf : ∀ n : ℕ, ∀ x ∈ Icc (β - 2 * δ) β, 0 < cRf n x ∧ ∀ e, cRf n x ≤ J e / (Real.exp (x * J e) - 1))
  (hident : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Icc (β - 2 * δ) β, Sig (fun n x => Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x)) n x * (cRf n x * (1 - Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x))) = 4 * ((n : ℝ) * Dseq n x / 4))
  (hSpoly : ∀ n : ℕ, N ≤ n → Sig (fun n x => Lindeberg.mean (fkMass (Gf n) (pf n x) 2) (ff n x)) n β ≤ (n : ℝ) ^ (1 - α)) :
-- imply
  ∃ Q : ℝ, 0 < Q ∧ ∀ n : ℕ, 1 ≤ n → Lindeberg.mean (fkMass (Gf n) (pf n (β - 2 * δ)) 2) (ff n (β - 2 * δ)) ≤ M * Real.exp (-(((n : ℝ) / Q) * δ)) := by
-- proof
  apply StatMech.Walls.oc4_fk_sharp_subcritical_fullyDischarged Gf pf ff mdim σf Rfam Dseq θ' J cRf α δ β M N hδ hα hα1 hMnn hN hJ hxpos hp hp1 hfmono hf0 hf1 hidem hDpos hreach hsum hd hθM hθlt1 hθmono hSpos hderiv hcRf hident hSpoly


-- created on 2026-10-23
