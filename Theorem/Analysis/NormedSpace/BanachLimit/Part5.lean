import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Def.Analysis.NormedSpace.BanachLimit.Part5
/-!
# Banach limits on bounded real sequences

A Banach limit is a positive shift-invariant continuous real-linear functional
on `ℕ →ᵇ ℝ` extending ordinary limits. Following Banach, the ordinary limit
functional on convergent sequences is dominated by the sublinear functional
`M x = limsup (Cesàro means of x)` and extended by Hahn–Banach
(`exists_extension_of_le_sublinear`); the bound `|L| ≤ ‖·‖` gives continuity,
and shift-invariance holds because the Cesàro means of `Sx - x` telescope to
`(x n - x 0) / n → 0`.

Source: S. Banach, *Théorie des opérations linéaires* (1932); G. G. Lorentz,
"A contribution to the theory of divergent sequences", *Acta Mathematica* 80
(1948), 167–190, DOI `10.1007/BF02393648`.
-/


namespace FunctionalAnalysis.BanachLimit

open scoped BoundedContinuousFunction

noncomputable section

lemma banachFunctional_convergent (x : BoundedSeq) (a : ℝ)
    (h : Filter.Tendsto (fun n => x n) Filter.atTop (nhds a)) :
    banachFunctional x = a :=
  (Classical.choose_spec exists_banachFunctional).1 x a h

lemma banachFunctional_nonneg (x : BoundedSeq) (h : ∀ n, 0 ≤ x n) :
    0 ≤ banachFunctional x :=
  (Classical.choose_spec exists_banachFunctional).2.1 x h

lemma banachFunctional_shift (x : BoundedSeq) :
    banachFunctional (shift x - x) = 0 :=
  (Classical.choose_spec exists_banachFunctional).2.2 x

lemma banachFunctional_one :
    banachFunctional (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1 :=
  banachFunctional_convergent _ _ tendsto_const_nhds

lemma banachFunctional_shift_eq (f g : BoundedSeq) (h : ∀ n, g n = f (n + 1)) :
    banachFunctional f = banachFunctional g := by
  have e : shift f = g := by
    apply BoundedContinuousFunction.ext
    intro n
    rw [shift_apply]
    exact (h n).symm
  have h0 := banachFunctional_shift f
  rw [e, map_sub] at h0
  exact (sub_eq_zero.mp h0).symm

/--
There exists a Banach limit `L : (ℕ →ᵇ ℝ) →L[ℝ] ℝ` on bounded real sequences that is positive on
pointwise nonnegative sequences, satisfies `L 1 = 1` for the constant-one sequence, is invariant
under the left shift `g n = f (n+1)`, and extends ordinary limits in that `f n → l` implies `L f =
l`. Source: S. Banach, Theorie des operations lineaires, 1932, definition of generalised limit; G.
Lorentz, Acta Math. 80 (1948) 167-190; Lean formalizes ℓ∞ via `BoundedContinuousFunction ℕ ℝ`.
-/
public theorem banach_limit :
    ∃ L : BoundedContinuousFunction ℕ ℝ →L[ℝ] ℝ,
      (∀ f : BoundedContinuousFunction ℕ ℝ, (∀ n, 0 ≤ f n) → 0 ≤ L f) ∧
      L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1 ∧
      (∀ (f g : BoundedContinuousFunction ℕ ℝ), (∀ n, g n = f (n + 1)) → L f = L g) ∧
      (∀ (f : BoundedContinuousFunction ℕ ℝ) (l : ℝ),
        Filter.Tendsto (fun n => f n) Filter.atTop (nhds l) → L f = l) :=
  ⟨banachFunctional, banachFunctional_nonneg, banachFunctional_one,
    fun f g h => banachFunctional_shift_eq f g h,
    fun f l h => banachFunctional_convergent f l h⟩

end
end FunctionalAnalysis.BanachLimit
