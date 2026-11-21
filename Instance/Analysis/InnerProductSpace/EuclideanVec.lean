module

public import Abbrev.Analysis.InnerProductSpace.EuclideanVec

/-!
# Euclidean coordinate vectors

## Coercion of coordinate vectors into Euclidean vectors

Mathlib coerces `EuclideanVec d` down to `Fin d → ℝ` (via `WithLp.ofLp`), but there is no coercion
in the other direction. A mixed expression such as `v - f` with `v : EuclideanVec d` and
`f : Fin d → ℝ` is therefore elaborated by coercing `v` down and subtracting in `Fin d → ℝ`.

The `Coe` instance below is what the expression tree elaborator (`binop%`, see `Lean.Elab.Extra`)
uses when it computes the supremum type of a `+` / `-` / `•` tree: it takes the expected type
`EuclideanVec d` as the initial supremum and only falls back to the coordinate space when the
leaves cannot be coerced there. With the instance, `f` is coerced up with `WithLp.toLp 2` and the
subtraction happens in `EuclideanVec d`, definitionally `WithLp.toLp 2 (WithLp.ofLp v - f)`.

It is a plain `Coe` at default priority (not `CoeTail` / `CoeHead`) so that `coerceSimple?` sees it
and the supremum computation stays on `EuclideanVec d`. Sites whose expected type is
`Fin d → ℝ` are unchanged: the supremum is then the coordinate space and `WithLp.ofLp` is
inserted on the Euclidean operand as before.

## Broadcast subtraction from a family of Euclidean vectors

`∇[x] F x` for a vector-valued `F` is a family `ι → EuclideanSpace 𝕜 κ`, while the `ᵥ*` result is a
coordinate vector `κ → 𝕜`. The `HSub` instance below subtracts that one vector from every row, so
the family subtraction can be factored out of `fun j => …`.

The second argument is spelled `κ → 𝕜`, not `EuclideanSpace 𝕜 κ`: since `EuclideanSpace 𝕜 κ` is
`WithLp 2 (κ → 𝕜)`, the right operand is elaborated as its coordinate function and typeclass
search then runs on that type, without inserting the upward `WithLp.toLp` coercion first. For the
same reason the more symmetric `HSub (ι → E) E (ι → E)` form never matches. This is an asymmetric
broadcast, like the existing `HSub (Matrix m n α) α (Matrix m n α)`: there is no per-row
`f i - v i` reading, which would be the distinct shape `(ι → κ → 𝕜)`.

Same-type family subtraction `f - g` with `g : ι → EuclideanSpace 𝕜 κ` still uses the Pi instance.
The Pi instance cannot replace this broadcast instance: for the goal above (in the `κ = ι` case,
where `κ → 𝕜` and `ι → β` are the same type) it would need
`HSub (EuclideanSpace 𝕜 κ) 𝕜 (EuclideanSpace 𝕜 κ)`, i.e. subtracting a scalar from a vector,
which does not exist. This is therefore the only applicable instance, so it needs no priority
annotation. Subtraction of Euclidean vectors is the `WithLp` `AddCommGroup` operation, hence the
`AddCommGroup 𝕜` assumption.
-/

@[expose] public section

instance {d : ℕ} : Coe (Fin d → ℝ) (EuclideanVec d) :=
  ⟨WithLp.toLp 2⟩

namespace EuclideanVec

instance {ι κ 𝕜 : Type*} [AddCommGroup 𝕜] :
    HSub (ι → EuclideanSpace 𝕜 κ) (κ → 𝕜) (ι → EuclideanSpace 𝕜 κ) where
  hSub f v i := f i - WithLp.toLp 2 v

/-- Component `i` of the broadcast subtraction: subtract the same Euclidean vector `v` from
`f i`. This is definitional, so `rfl` also closes goals of this shape. -/
@[simp] theorem sub_apply {ι κ 𝕜 : Type*} [AddCommGroup 𝕜]
    (f : ι → EuclideanSpace 𝕜 κ) (v : κ → 𝕜) (i : ι) :
    (f - v) i = f i - WithLp.toLp 2 v :=
  rfl

end EuclideanVec
