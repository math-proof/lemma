import Mathlib.Topology.Algebra.Constructions
import sympy.series.limits
import sympy.Basic


open Filter


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ : ℝ} :
-- imply
  Filter.limUnder (nhdsWithin x₀ {x₀}ᶜ) (fun x => f (x - x₀)) =
    Filter.limUnder (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) f := by
-- proof
  let e : ℝ ≃ₜ ℝ := Homeomorph.addRight (-x₀)
  have he : (e : ℝ → ℝ) = fun x => x - x₀ := by
    funext x
    simp [e, sub_eq_add_neg]
  have he0 : e x₀ = 0 := by
    rw [he]
    ring
  have hmap : map e (nhdsWithin x₀ {x₀}ᶜ) = nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ := by
    rw [e.map_punctured_nhds_eq x₀, he0]
  have hcomp : (fun x => f (x - x₀)) = f ∘ e := by
    funext x
    simp [he]
  have hkey : map (f ∘ e) (nhdsWithin x₀ {x₀}ᶜ) =
      map f (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) := by
    rw [← map_map, hmap]
  simp only [limUnder, hcomp, hkey]


-- created on 2020-04-05
