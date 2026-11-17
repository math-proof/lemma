module

public import Mathlib
public import Def.WeierstrassCurve_OddOrderSummingSet

public section

namespace WeierstrassCurve

namespace Affine.Point

variable {R : Type*} [CommRing R] {W : Affine R}


@[simp] public theorem coordsOrZero_zero : ((.zero : W.Point)).coordsOrZero = (0, 0) := rfl

@[simp] public theorem coordsOrZero_some {x y : R} (h : W.Nonsingular x y) :
    (Point.some x y h).coordsOrZero = (x, y) := rfl

end Affine.Point

section SummingSet

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)


public theorem mem_oddOrderSummingSet {Q : W.toAffine.Point} {n : ℕ} {P : F × F} :
    P ∈ W.oddOrderSummingSet Q n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ (k • Q).coordsOrZero = P := by
  simp only [oddOrderSummingSet, Finset.mem_image, Finset.mem_Icc]
  exact ⟨fun ⟨k, ⟨h1, h2⟩, h3⟩ => ⟨k, h1, h2, h3⟩, fun ⟨k, h1, h2, h3⟩ => ⟨k, ⟨h1, h2⟩, h3⟩⟩

end SummingSet

end WeierstrassCurve
