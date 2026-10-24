import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanExteriorClosure
open Set SimpleGraph StatMech StatMech.Lattice


/--
[jec_mem_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_mem_quad_eq
  {z p : Site 2} :
-- imply
  p ∈ jec_quad z ↔ p 0 ≤ z 0 - 1 ∧ p 1 ≤ z 1 - 1 := by
-- proof
  apply StatMech.Lattice.jec_mem_quad z p

/--
[jec_rayEdge_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rayEdge_mk_eq
  {z x y : Site 2} :
-- imply
  jec_rayEdge z s(x, y) ↔ (x 0 = y 0 ∧ x 0 ≤ z 0 - 1) ∧ ((x 1 = z 1 - 1 ∧ y 1 = z 1) ∨ (y 1 = z 1 - 1 ∧ x 1 = z 1)) := by
-- proof
  apply StatMech.Lattice.jec_rayEdge_mk z x y

/--
[jec_wallEdge_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_wallEdge_mk_eq
  {z x y : Site 2} :
-- imply
  jec_wallEdge z s(x, y) ↔ (x 1 = y 1 ∧ x 1 ≤ z 1 - 1) ∧ ((x 0 = z 0 - 1 ∧ y 0 = z 0) ∨ (y 0 = z 0 - 1 ∧ x 0 = z 0)) := by
-- proof
  apply StatMech.Lattice.jec_wallEdge_mk z x y

/--
[jec_quad_bdEdge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_quad_bdEdge_iff_eq
  {z u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  bdEdge (jec_quad z) s(u, v) ↔ (jec_rayEdge z s(u, v) ∨ jec_wallEdge z s(u, v)) := by
-- proof
  apply StatMech.Lattice.jec_quad_bdEdge_iff z u v hadj

/--
[jec_ray_wall_excl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_ray_wall_excl_eq
  {z u v : Site 2} :
-- imply
  ¬ (jec_rayEdge z s(u, v) ∧ jec_wallEdge z s(u, v)) := by
-- proof
  apply StatMech.Lattice.jec_ray_wall_excl z u v

/--
[jec_rayCount_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rayCount_nil_eq
  {z x : Site 2} :
-- imply
  jec_rayCount z (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
-- proof
  apply StatMech.Lattice.jec_rayCount_nil z x

/--
[jec_wallCount_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_wallCount_nil_eq
  {z x : Site 2} :
-- imply
  jec_wallCount z (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
-- proof
  apply StatMech.Lattice.jec_wallCount_nil z x

/--
[jec_rayCount_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rayCount_append_eq
  {z : Site 2}
  {x y w' : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
  {q : (hypercubicLattice 2).Walk y w'} :
-- imply
  jec_rayCount z (p.append q) = jec_rayCount z p + jec_rayCount z q := by
-- proof
  apply StatMech.Lattice.jec_rayCount_append z p q

/--
[jec_rayCount_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rayCount_copy_eq
  {z : Site 2}
  {x y x' y' : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hu : x = x')
  (hv : y = y') :
-- imply
  jec_rayCount z (w.copy hu hv) = jec_rayCount z w := by
-- proof
  apply StatMech.Lattice.jec_rayCount_copy z w hu hv

/--
[jec_rayCount_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rayCount_reverse_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  jec_rayCount z w.reverse = jec_rayCount z w := by
-- proof
  apply StatMech.Lattice.jec_rayCount_reverse z w

/--
[jec_crossCount_quad_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_crossCount_quad_decomp_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  crossCount (jec_quad z) w = jec_rayCount z w + jec_wallCount z w := by
-- proof
  apply StatMech.Lattice.jec_crossCount_quad_decomp z w

/--
[jec_rayCount_horizontalStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rayCount_horizontalStep_eq
  {z z' : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hz'0 : z' 0 = z 0 + 1)
  (hz'1 : z' 1 = z 1)
  (hz : z ∉ w.support) :
-- imply
  jec_rayCount z' w = jec_rayCount z w := by
-- proof
  apply StatMech.Lattice.jec_rayCount_horizontalStep z z' hz'0 hz'1 w hz

/--
[jec_wallCount_verticalStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_wallCount_verticalStep_eq
  {z z' : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hz'0 : z' 0 = z 0)
  (hz'1 : z' 1 = z 1 + 1)
  (hz : z ∉ w.support) :
-- imply
  jec_wallCount z' w = jec_wallCount z w := by
-- proof
  apply StatMech.Lattice.jec_wallCount_verticalStep z z' hz'0 hz'1 w hz

/--
[jec_loop_ray_wall_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_loop_ray_wall_parity_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  Even (jec_rayCount z Vc) ↔ Even (jec_wallCount z Vc) := by
-- proof
  apply StatMech.Lattice.jec_loop_ray_wall_parity z Vc

/--
[jec_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_localConstancy_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) := by
-- proof
  apply StatMech.Lattice.jec_localConstancy Vc hadj hu hv

/--
[jec_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_mem_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  z ∈ jec_leftRegion Vc ↔ ¬ Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Lattice.jec_mem_leftRegion Vc z

/--
[jec_leftRegion_bdEdge_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_leftRegion_bdEdge_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.jec_leftRegion_bdEdge_support Vc hadj hbd

/--
[jec_rayCount_vsegUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rayCount_vsegUp_eq
  {z : Site 2}
  {col r : ℤ}
  {k : ℕ} :
-- imply
  jec_rayCount z (jec_vsegUp col r k) = (if col ≤ z 0 - 1 ∧ r ≤ z 1 - 1 ∧ z 1 - 1 ≤ r + (k:ℤ) - 1 then 1 else 0) := by
-- proof
  apply StatMech.Lattice.jec_rayCount_vsegUp z col r k

/--
[jec_rayCount_hsegRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rayCount_hsegRight_eq
  {z : Site 2}
  {row t : ℤ}
  {k : ℕ} :
-- imply
  jec_rayCount z (jec_hsegRight row t k) = 0 := by
-- proof
  apply StatMech.Lattice.jec_rayCount_hsegRight z row t k

/--
[jec_vsegUp_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_vsegUp_support_eq
  {col r : ℤ}
  {k : ℕ}
  {p : Site 2}
-- given
  (hp : p ∈ (jec_vsegUp col r k).support) :
-- imply
  p 0 = col ∧ r ≤ p 1 ∧ p 1 ≤ r + (k:ℤ) := by
-- proof
  apply StatMech.Lattice.jec_vsegUp_support col r k hp

/--
[jec_hsegRight_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_hsegRight_support_eq
  {row t : ℤ}
  {k : ℕ}
  {p : Site 2}
-- given
  (hp : p ∈ (jec_hsegRight row t k).support) :
-- imply
  p 1 = row ∧ t ≤ p 0 ∧ p 0 ≤ t + (k:ℤ) := by
-- proof
  apply StatMech.Lattice.jec_hsegRight_support row t k hp

/--
[jec_rayCount_retPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rayCount_retPath_eq
  {z : Site 2}
  {α a0 b0 c d : ℤ}
-- given
  (ha : α ≤ a0)
  (hb : α ≤ b0)
  (hcd : c ≤ d) :
-- imply
  jec_rayCount z (jec_retPath α a0 b0 c d ha hb hcd) = (if b0 ≤ z 0 - 1 ∧ d ≤ z 1 - 1 ∧ z 1 - 1 ≤ d then 1 else 0) + (if α-1 ≤ z 0 - 1 ∧ c-1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ (c-1) + ((d+1-(c-1)).toNat:ℤ) - 1 then 1 else 0) + (if a0 ≤ z 0 - 1 ∧ c-1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ c-1 then 1 else 0) := by
-- proof
  apply StatMech.Lattice.jec_rayCount_retPath z α a0 b0 c d ha hb hcd

/--
[jec_retPath_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_retPath_support_eq
  {α a0 b0 c d : ℤ}
  {p : Site 2}
-- given
  (ha : α ≤ a0)
  (hb : α ≤ b0)
  (hcd : c ≤ d)
  (hp : p ∈ (jec_retPath α a0 b0 c d ha hb hcd).support) :
-- imply
  p 0 = α - 1 ∨ p 1 = c - 1 ∨ p 1 = d + 1 ∨ p = ![b0, d] ∨ p = ![a0, c] := by
-- proof
  apply StatMech.Lattice.jec_retPath_support α a0 b0 c d ha hb hcd hp

/--
[jec_retPath_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_retPath_col_eq
  {α β a0 b0 c d : ℤ}
  {p : Site 2}
-- given
  (ha : α ≤ a0)
  (hb : α ≤ b0)
  (hcd : c ≤ d)
  (haβ : a0 ≤ β)
  (hbβ : b0 ≤ β)
  (hαβ : α ≤ β)
  (hp : p ∈ (jec_retPath α a0 b0 c d ha hb hcd).support) :
-- imply
  α - 1 ≤ p 0 ∧ p 0 ≤ β := by
-- proof
  apply StatMech.Lattice.jec_retPath_col α β a0 b0 c d ha hb hcd haβ hbβ hαβ hp

/--
[jec_mem_belowSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_mem_belowSet_eq
  {y : ℤ}
  {p : Site 2} :
-- imply
  p ∈ jec_belowSet y ↔ p 1 ≤ y - 1 := by
-- proof
  apply StatMech.Lattice.jec_mem_belowSet y p

/--
[jec_belowSet_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_belowSet_bdEdge_eq
  {y : ℤ}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  bdEdge (jec_belowSet y) s(u, v) ↔ (u 0 = v 0) ∧ ((u 1 = y - 1 ∧ v 1 = y) ∨ (v 1 = y - 1 ∧ u 1 = y)) := by
-- proof
  apply StatMech.Lattice.jec_belowSet_bdEdge y u v hadj

/--
[jec_ray_eq_below](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_ray_eq_below_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hfar : ∀ p ∈ w.support, p 0 ≤ z 0 - 1) :
-- imply
  jec_rayCount z w = crossCount (jec_belowSet (z 1)) w := by
-- proof
  apply StatMech.Lattice.jec_ray_eq_below z w hfar

/--
[jec_ray_even_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_ray_even_far_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ Vc.support, p 0 ≤ z 0 - 1) :
-- imply
  Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Lattice.jec_ray_even_far Vc z hfar

/--
[jec_rayCount_eq_zero_of_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rayCount_eq_zero_of_right_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : ∀ p ∈ w.support, z 0 ≤ p 0) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Lattice.jec_rayCount_eq_zero_of_right z w h

/--
[jec_arcSeparatingSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_arcSeparatingSet_eq
  {α β c d a0 b0 : ℤ}
  {V : (hypercubicLattice 2).Walk ![a0, c] ![b0, d]}
  {P : Set (Site 2)}
-- given
  (hαβ : α < β)
  (hcd : c ≤ d)
  (ha0 : α ≤ a0)
  (ha0' : a0 ≤ β)
  (hb0 : α ≤ b0)
  (hb0' : b0 ≤ β)
  (hVbox : ∀ p ∈ V.support, p ∈ rect α β c d)
  (hVP : ∀ p ∈ V.support, p ∈ P) :
-- imply
  ArcSeparatingSet P α β c d := by
-- proof
  apply StatMech.Lattice.jec_arcSeparatingSet α β c d a0 b0 hαβ hcd ha0 ha0' hb0 hb0' V hVbox P hVP

/--
[jec_vsFix_arc_sides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_vsFix_arc_sides_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
-- given
  (hαβ : α < β)
  (hcd : c ≤ d) :
-- imply
  StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
-- proof
  apply StatMech.Lattice.jec_vsFix_arc_sides ω hαβ hcd

/--
[jec_rsw_strip_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean)
-/
@[path]
private lemma jec_rsw_strip_glue_eq
  {μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2)))}
  [MeasureTheory.IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
-- given
  (hpa : StatMech.Universality.PositivelyAssociated μ)
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c ≤ d) :
-- imply
  μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d) * μ.real (horizontalCrossingEvent m b c d) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Lattice.jec_rsw_strip_glue μ hpa ham hmm' hm'b hamL hmbR hcd


-- created on 2026-10-23
