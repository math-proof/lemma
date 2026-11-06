import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Real.Hyperreal
import Lemma.Hyperreal.XEq.of.InfinitesimalSub
import Syntax.Analysis.Real.Limits
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 400000
open Real Hyperreal Filter ArchimedeanClass


/--
NSA difference quotient (microaffinity) from a pointwise derivative.

If `HasDerivAt g g' x` and `Δx → 0⁺`, then
`(Germ.map g (↑x+Δx) - ↑(g x)) / Δx ≈ ↑g'`.

General form of the constant-derivative equality
`SubMapAddCoe.eq.MulDeriv.of.All_HasDerivAt_Deriv`.
-/
@[path]
private lemma main
  {g : ℝ → ℝ}
  {g' : ℝ}
  {x : ℝ}
  {Δx : ℝ*}
-- given
  (hg : HasDerivAt g g' x)
  (h_Δx : Δx → 0⁺) :
-- imply
  ((show ℝ* from Germ.map g ((x : ℝ*) + Δx)) - ↑(g x)) / Δx ≈ ↑g' := by
-- proof
  apply XEq.of.InfinitesimalSub
  rcases ofSeq_surjective Δx with ⟨d, rfl⟩
  -- `ofSeq d > 0` and infinitesimal.
  have hd_pos : ∀ᶠ n in hyperfilter ℕ, (0 : ℝ) < d n :=
    ofSeq_lt_ofSeq.mp h_Δx.1
  have hmk : 0 < mk (ofSeq d) := h_Δx.2
  have hst : stdPart (ofSeq d) = 0 :=
    stdPart_eq_zero.2 hmk.ne'
  have hx_le : 0 ≤ mk (ofSeq d) := hmk.le
  have hΔ_tendsto : (ofSeq d).Tendsto (nhds (0 : ℝ)) := by
    rw [tendsto_iff_forall]
    constructor <;> intro s hs
    ·
      exact (lt_of_lt_stdPart coeRingHom hx_le (by rwa [hst])).le
    ·
      exact (lt_of_stdPart_lt coeRingHom hx_le (by rwa [hst])).le
  have hd_tendsto : Tendsto d (hyperfilter ℕ) (nhds (0 : ℝ)) :=
    (tendsto_ofSeq).1 hΔ_tendsto
  have hd_nhdsPos : Tendsto d (hyperfilter ℕ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_inf.2 ⟨hd_tendsto, tendsto_principal.2 hd_pos⟩
  have hslope :
      Tendsto (fun t : ℝ => (g (x + t) - g x) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds g') := by
    convert hg.tendsto_slope_zero_right using 1
    funext t
    change (g (x + t) - g x) / t = t⁻¹ • (g (x + t) - g x)
    simp [div_eq_inv_mul, smul_eq_mul]
  have hcomp :
      Tendsto (fun n : ℕ => (g (x + d n) - g x) / d n) (hyperfilter ℕ) (nhds g') :=
    hslope.comp hd_nhdsPos
  -- Match SubMapAddCoe rewrite style (all Germ, no `show ℝ*`).
  change
    ((Germ.map g
        ((↑x : Germ (hyperfilter ℕ : Filter ℕ) ℝ) +
          (↑d : Germ (hyperfilter ℕ : Filter ℕ) ℝ)) -
      (↑(g x) : Germ (hyperfilter ℕ : Filter ℕ) ℝ)) /
        (↑d : Germ (hyperfilter ℕ : Filter ℕ) ℝ) -
      (↑g' : Germ (hyperfilter ℕ : Filter ℕ) ℝ)) → 0
  have hx : (↑x : Germ (hyperfilter ℕ : Filter ℕ) ℝ) = ↑(fun _ : ℕ => x) := rfl
  have hgx : (↑(g x) : Germ (hyperfilter ℕ : Filter ℕ) ℝ) = ↑(fun _ : ℕ => g x) := rfl
  have hg'coe : (↑g' : Germ (hyperfilter ℕ : Filter ℕ) ℝ) = ↑(fun _ : ℕ => g') := rfl
  rw [hx, hgx, hg'coe, (Germ.coe_add (fun _ : ℕ => x) d).symm, Germ.map_coe]
  have hcomp' : g ∘ ((fun _ : ℕ => x) + d) = fun n => g (x + d n) := by
    funext n; rfl
  rw [hcomp', (Germ.coe_sub (fun n : ℕ => g (x + d n)) (fun _ : ℕ => g x)).symm]
  have hfun :
      ((fun n : ℕ => g (x + d n)) - fun _ : ℕ => g x) = fun n => g (x + d n) - g x :=
    rfl
  rw [hfun, (Germ.coe_div (fun n : ℕ => g (x + d n) - g x) d).symm]
  have hfun' :
      ((fun n : ℕ => g (x + d n) - g x) / d) = fun n => (g (x + d n) - g x) / d n :=
    rfl
  rw [hfun', (Germ.coe_sub (fun n : ℕ => (g (x + d n) - g x) / d n) (fun _ : ℕ => g')).symm]
  have hdiff :
      Tendsto (fun n => (g (x + d n) - g x) / d n - g') (hyperfilter ℕ) (nhds 0) := by
    simpa using hcomp.sub (tendsto_const_nhds (x := g'))
  exact archimedeanClassMk_pos_of_tendsto <|
    (tendsto_ofSeq (f := fun n => (g (x + d n) - g x) / d n - g')).2 hdiff


-- created on 2026-11-05
