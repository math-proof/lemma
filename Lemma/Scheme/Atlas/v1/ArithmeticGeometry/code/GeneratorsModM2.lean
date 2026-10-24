import Mathlib
import sympy.Basic


/--
[Ideal.generators_iff_cotangent_span](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GeneratorsModM2.lean)
-/
@[path]
lemma Ideal.generators_iff_cotangent_span
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R]
  {s : Set (IsLocalRing.maximalIdeal R)} :
-- imply
  Ideal.span (Subtype.val '' s) = IsLocalRing.maximalIdeal R ↔ Submodule.span (IsLocalRing.ResidueField R) ((IsLocalRing.maximalIdeal R).toCotangent '' s) = ⊤ := by
-- proof
  rw [← Ideal.submodule_span_eq, Submodule.span_val_image_eq_iff,
    IsLocalRing.CotangentSpace.span_image_eq_top_iff]

/--
[Ideal.generators_iff_cotangent_span_fin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GeneratorsModM2.lean)
-/
@[path]
lemma Ideal.generators_iff_cotangent_span_fin
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R]
  {n : ℕ}
  {t : Fin n → IsLocalRing.maximalIdeal R} :
-- imply
  Ideal.span (Set.range (fun i => (t i : R))) = IsLocalRing.maximalIdeal R ↔ Submodule.span (IsLocalRing.ResidueField R) (Set.range (fun i => (IsLocalRing.maximalIdeal R).toCotangent (t i))) = ⊤ := by
-- proof
  rw [show Set.range (fun i => (t i : R)) = Subtype.val '' (Set.range t) from by
    ext x; simp [Set.mem_image, Set.mem_range],
    show Set.range (fun i => (IsLocalRing.maximalIdeal R).toCotangent (t i)) =
      (IsLocalRing.maximalIdeal R).toCotangent '' (Set.range t) from by
      ext x; simp [Set.mem_image, Set.mem_range]]
  exact Ideal.generators_iff_cotangent_span R (Set.range t)


-- created on 2026-10-23
