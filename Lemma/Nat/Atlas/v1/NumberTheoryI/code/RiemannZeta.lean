import Mathlib
import Initialize.Tactic.Attr.Basic
open Complex Filter Topology Nat


namespace RiemannZetaFunction

/--
[riemannZeta_eq_tsum_one_div_nat_cpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RiemannZeta.lean)
-/
@[path]
lemma riemannZeta_eq_tsum_one_div_nat_cpow
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  riemannZeta s = ∑' n : ℕ, 1 / (↑n : ℂ) ^ s :=
-- proof
  zeta_eq_tsum_one_div_nat_cpow hs

end RiemannZetaFunction

namespace RiemannZetaFunction

/--
[riemannZeta_eulerProduct_hasProd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RiemannZeta.lean)
-/
@[path]
lemma riemannZeta_eulerProduct_hasProd
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  HasProd (fun p : Nat.Primes ↦ (1 - (↑(↑p) : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
-- proof
  _root_.riemannZeta_eulerProduct_hasProd hs

end RiemannZetaFunction

namespace RiemannZetaFunction

/--
[riemannZeta_ne_zero_of_one_lt_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RiemannZeta.lean)
-/
@[path]
lemma riemannZeta_ne_zero_of_one_lt_re
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  riemannZeta s ≠ 0 :=
-- proof
  _root_.riemannZeta_ne_zero_of_one_lt_re hs

end RiemannZetaFunction

namespace RiemannZetaFunction

/--
[riemannZeta_eulerProduct_and_nonvanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RiemannZeta.lean)
-/
@[path]
lemma riemannZeta_eulerProduct_and_nonvanishing
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  HasProd (fun p : Nat.Primes ↦ (1 - (↑(↑p) : ℂ) ^ (-s))⁻¹) (riemannZeta s) ∧ riemannZeta s ≠ 0 :=
-- proof
  ⟨riemannZeta_eulerProduct_hasProd hs, riemannZeta_ne_zero_of_one_lt_re hs⟩

end RiemannZetaFunction

namespace RiemannZetaFunction

/--
[riemannZeta_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RiemannZeta.lean)
-/
@[path]
lemma riemannZeta_differentiableAt
  {s : ℂ}
-- given
  (hs : s ≠ 1) :
-- imply
  DifferentiableAt ℂ riemannZeta s :=
-- proof
  differentiableAt_riemannZeta hs

end RiemannZetaFunction

namespace RiemannZetaFunction

/--
[riemannZeta_residue_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RiemannZeta.lean)
-/
@[path]
lemma riemannZeta_residue_eq_one
-- imply
  Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
-- proof
  riemannZeta_residue_one

end RiemannZetaFunction

namespace RiemannZetaFunction

/--
[riemannZeta_meromorphic_with_residue](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RiemannZeta.lean)
-/
@[path]
lemma riemannZeta_meromorphic_with_residue
-- imply
  (∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ riemannZeta s) ∧ Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
-- proof
  ⟨fun _ hs ↦ riemannZeta_differentiableAt hs, riemannZeta_residue_eq_one⟩

end RiemannZetaFunction

namespace RiemannZetaFunction

/--
[mertens_norm_zeta_product_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RiemannZeta.lean)
-/
@[path]
lemma mertens_norm_zeta_product_ge_one
  {x y : ℝ}
-- given
  (hx : 1 < x) :
-- imply
  ‖riemannZeta (↑x) ^ 3 * riemannZeta (↑x + ↑y * Complex.I) ^ 4 * riemannZeta (↑x + 2 * ↑y * Complex.I)‖ ≥ 1 := by
-- proof
  have hx'_pos : (0 : ℝ) < x - 1 := by linarith
  have hmathlib := DirichletCharacter.norm_LFunction_product_ge_one
    (1 : DirichletCharacter ℂ 1) hx'_pos y
  simp only [DirichletCharacter.LFunction_modOne_eq] at hmathlib
  have harg : (1 : ℂ) + (↑(x - 1) : ℂ) = ↑x := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one]; ring
  rw [harg] at hmathlib
  convert hmathlib using 3 <;> ring_nf

end RiemannZetaFunction

namespace RiemannZetaFunction

/--
[riemannZeta_ne_zero_of_one_le_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RiemannZeta.lean)
-/
@[path]
lemma riemannZeta_ne_zero_of_one_le_re
  {s : ℂ}
-- given
  (hs : 1 ≤ s.re) :
-- imply
  riemannZeta s ≠ 0 :=
-- proof
  _root_.riemannZeta_ne_zero_of_one_le_re hs

end RiemannZetaFunction


-- created on 2026-10-23
