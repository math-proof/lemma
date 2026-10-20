import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.PanVandermonde
open MetaMathlibExt


/--
[pan_vandermonde_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PanVandermonde.lean)
-/
@[path]
private lemma pan_vandermonde_general_eq
  [RCLike K]
  {p : ℕ}
  {x : Fin p → K}
  {α β γ : ℝ}
  {S : ℝ → ℝ → ℝ → ℕ → ℕ → K}
-- given
  (hS : ∀ (a b c : ℝ) (y : K) (n : ℕ), (∏ j ∈ Finset.range n, (y - (j : K) * RCLike.ofReal a)) = ∑ k ∈ Finset.range (n + 1), S a b c n k * ∏ j ∈ Finset.range k, ((y - RCLike.ofReal c) - (j : K) * RCLike.ofReal b))
  (hSvan : ∀ (a b c : ℝ) (n k : ℕ), n < k → S a b c n k = 0)
  (hdist : Function.Injective x) :
-- imply
  (Matrix.of (fun (r c : Fin p) => ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)) =
    Matrix.of (fun (r c : Fin p) => S α β γ r.val c.val) *
    Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, ((x c - RCLike.ofReal γ) - (j : K) * RCLike.ofReal β)))
    ∧ Matrix.det (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α))) =
    Matrix.det (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0)))
    ∧ Matrix.det (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0))) =
    ∏ ij ∈ Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2), (x ij.2 - x ij.1)
    ∧ IsUnit (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))
    ∧ (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))⁻¹ =
    (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0)))⁻¹ *
    Matrix.of (fun (r c : Fin p) => S 0 α 0 r.val c.val) := by
-- proof
  apply MetaMathlibExt.pan_vandermonde_general p K x α β γ S hS hSvan hdist

/--
[pan_vandermonde](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PanVandermonde.lean)
-/
@[path]
private lemma pan_vandermonde_eq
  :
-- imply
  ∀ (p : ℕ)
    (hp : 0 < p)
    (K : Type*) [RCLike K]
    (x : Fin p → K)
    (α β γ : ℝ)
    (S : ℝ → ℝ → ℝ → ℕ → ℕ → K)
    (hS : ∀ (a b c : ℝ) (y : K) (n : ℕ),
    (∏ j ∈ Finset.range n, (y - (j : K) * RCLike.ofReal a)) =
    ∑ k ∈ Finset.range (n + 1),
    S a b c n k * ∏ j ∈ Finset.range k,
    ((y - RCLike.ofReal c) - (j : K) * RCLike.ofReal b))
    (hSvan : ∀ (a b c : ℝ) (n k : ℕ), n < k → S a b c n k = 0)
    (hdist : Function.Injective x),
    (Matrix.of (fun (r c : Fin p) => ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)) =
    Matrix.of (fun (r c : Fin p) => S α β γ r.val c.val) *
    Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, ((x c - RCLike.ofReal γ) - (j : K) * RCLike.ofReal β)))
    ∧ Matrix.det (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α))) =
    Matrix.det (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0)))
    ∧ Matrix.det (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0))) =
    ∏ ij ∈ Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2), (x ij.2 - x ij.1)
    ∧ IsUnit (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))
    ∧ (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal α)))⁻¹ =
    (Matrix.of (fun (r c : Fin p) =>
    ∏ j ∈ Finset.range r.val, (x c - (j : K) * RCLike.ofReal 0)))⁻¹ *
    Matrix.of (fun (r c : Fin p) => S 0 α 0 r.val c.val) := by
-- proof
  apply MetaMathlibExt.pan_vandermonde


-- created on 2026-10-20
