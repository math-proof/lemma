module

public import Abbrev.Analysis.InnerProductSpace.EuclideanVec
public import Mathlib.Data.Matrix.Basic

/-!
# Coercion of a family of Euclidean vectors into a matrix

`∇[x] F x` for `F : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)` has type
`Fin n → EuclideanSpace ℝ (Fin n)`, i.e. one Euclidean vector per row, while `ᵥ*` expects its
right operand to be a `Matrix (Fin n) (Fin n) ℝ`, definitionally `Fin n → Fin n → ℝ`. Today such a
term has to be opened componentwise with `Matrix.of (fun i k => (∇[x] F x i) k)`.

The `Coe` instance below performs exactly that conversion: it reads the `k`-th coordinate of the
`i`-th Euclidean vector through the existing downward coercion `WithLp.ofLp`. It is a plain `Coe`
at default priority (not `CoeTail` / `CoeHead`), applies to any index types `ι`, `κ` and any
scalar `𝕜`, and coerces a family into nothing except a matrix, so it does not compete with the
downward `Coe (WithLp p V) V` or the upward `Coe (Fin d → ℝ) (EuclideanVec d)`.
-/

@[expose] public section

instance {ι κ 𝕜 : Type*} : Coe (ι → EuclideanSpace 𝕜 κ) (Matrix ι κ 𝕜) :=
  ⟨fun f i k => f i k⟩
