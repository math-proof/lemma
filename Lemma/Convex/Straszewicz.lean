import Mathlib
import sympy.Basic
import sympy.calculus.Straszewicz

open Convex.Straszewicz

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma convexHull_of_compact_is
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Set E}
  (hK : IsCompact K) :
-- imply
  IsCompact (convexHull ℝ K) := by
-- proof
  apply Convex.Straszewicz.IsCompact.convexHull_of_compact hK

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma convexOn_line_is
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E}
  (hconv : ConvexOn ℝ Set.univ h)
  (v : StrongDual ℝ E) :
-- imply
  ConvexOn ℝ Set.univ (fun s : ℝ => h (x + s • v)) := by
-- proof
  apply Convex.Straszewicz.convexOn_line hconv v

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma dirQuot_bddBelow_is
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E}
  (hconv : ConvexOn ℝ Set.univ h)
  (v : StrongDual ℝ E) :
-- imply
  BddBelow (dirQuot h x v) := by
-- proof
  apply Convex.Straszewicz.dirQuot_bddBelow hconv v

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma dirQuot_nonempty_is
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E}
  (v : StrongDual ℝ E) :
-- imply
  (dirQuot h x v).Nonempty := by
-- proof
  apply Convex.Straszewicz.dirQuot_nonempty v

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma dirDeriv_le_quot_le
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E} {t : ℝ}
  (hconv : ConvexOn ℝ Set.univ h)
  (ht : 0 < t)
  (v : StrongDual ℝ E) :
-- imply
  dirDeriv h x v ≤ (h (x + t • v) - h x) / t := by
-- proof
  apply Convex.Straszewicz.dirDeriv_le_quot hconv v ht

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma dirDeriv_subadd_le
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E}
  (hconv : ConvexOn ℝ Set.univ h)
  (v w : StrongDual ℝ E) :
-- imply
  dirDeriv h x (v + w) ≤ dirDeriv h x v + dirDeriv h x w := by
-- proof
  apply Convex.Straszewicz.dirDeriv_subadd hconv v w

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma dirDeriv_zero_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E} :
-- imply
  dirDeriv h x 0 = 0 := by
-- proof
  apply Convex.Straszewicz.dirDeriv_zero

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma dirDeriv_add_neg_nonneg_le
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E}
  (hconv : ConvexOn ℝ Set.univ h)
  (v : StrongDual ℝ E) :
-- imply
  0 ≤ dirDeriv h x v + dirDeriv h x (-v) := by
-- proof
  apply Convex.Straszewicz.dirDeriv_add_neg_nonneg hconv v

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma suppFunc_attain_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E}
  (hK : IsCompact K)
  (hKne : K.Nonempty)
  (l : StrongDual ℝ E) :
-- imply
  ∃ x ∈ K, l x = suppFunc K l := by
-- proof
  apply Convex.Straszewicz.suppFunc_attain hK hKne l

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma suppFunc_convex_is
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E}
  (hK : IsCompact K)
  (hKne : K.Nonempty) :
-- imply
  ConvexOn ℝ Set.univ (suppFunc K) := by
-- proof
  apply Convex.Straszewicz.suppFunc_convex hK hKne

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma suppFunc_lipschitz_le
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E}
  (hK : IsCompact K)
  (hKne : K.Nonempty) :
-- imply
  ∃ C : ℝ, 0 ≤ C ∧ ∀ l₁ l₂ : StrongDual ℝ E,
    suppFunc K l₁ - suppFunc K l₂ ≤ C * ‖l₁ - l₂‖ := by
-- proof
  apply Convex.Straszewicz.suppFunc_lipschitz hK hKne

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma suppFunc_continuous_is
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E}
  (hK : IsCompact K)
  (hKne : K.Nonempty) :
-- imply
  Continuous (suppFunc K) := by
-- proof
  apply Convex.Straszewicz.suppFunc_continuous hK hKne

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma dirDeriv_sublevel_open_is
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E}
  (hK : IsCompact K)
  (hKne : K.Nonempty)
  (v : StrongDual ℝ E)
  (c : ℝ) :
-- imply
  IsOpen {x | dirDeriv (suppFunc K) x v + dirDeriv (suppFunc K) x (-v) < c} := by
-- proof
  apply Convex.Straszewicz.dirDeriv_sublevel_open hK hKne v c

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma dirDeriv_continuous_in_v_is
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E}
  (hK : IsCompact K)
  (hKne : K.Nonempty)
  (x : StrongDual ℝ E) :
-- imply
  Continuous (fun w => dirDeriv (suppFunc K) x w) := by
-- proof
  apply Convex.Straszewicz.dirDeriv_continuous_in_v hK hKne x

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma dirDeriv_suppFunc_bound_le
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E} {C : ℝ}
  (hK : IsCompact K)
  (hKne : K.Nonempty)
  (hlip : ∀ l₁ l₂ : StrongDual ℝ E, suppFunc K l₁ - suppFunc K l₂ ≤ C * ‖l₁ - l₂‖)
  (x w : StrongDual ℝ E) :
-- imply
  dirDeriv (suppFunc K) x w ≤ C * ‖w‖ := by
-- proof
  apply Convex.Straszewicz.dirDeriv_suppFunc_bound hK hKne hlip x w

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma dense_gateaux_is
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Set E}
  (hK : IsCompact K)
  (hKne : K.Nonempty) :
-- imply
  Dense {l | GateauxPt (suppFunc K) l} := by
-- proof
  apply Convex.Straszewicz.dense_gateaux hK hKne

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma maximizer_dirDeriv_ge_le
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E} {u : StrongDual ℝ E} {z : E}
  (hK : IsCompact K)
  (hKne : K.Nonempty)
  (hzK : z ∈ K)
  (hmax : u z = suppFunc K u)
  (v : StrongDual ℝ E) :
-- imply
  v z ≤ dirDeriv (suppFunc K) u v := by
-- proof
  apply Convex.Straszewicz.maximizer_dirDeriv_ge hK hKne hzK hmax v

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma gateaux_unique_maximizer_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E} {l : StrongDual ℝ E} {z₁ z₂ : E}
  (hK : IsCompact K)
  (hKne : K.Nonempty)
  (hG : GateauxPt (suppFunc K) l)
  (h₁ : z₁ ∈ K)
  (h₂ : z₂ ∈ K)
  (e₁ : l z₁ = suppFunc K l)
  (e₂ : l z₂ = suppFunc K l) :
-- imply
  z₁ = z₂ := by
-- proof
  apply Convex.Straszewicz.gateaux_unique_maximizer hK hKne hG h₁ h₂ e₁ e₂

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma unique_maximizer_exposed_is
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Set E} {l : StrongDual ℝ E} {z : E}
  (hK : IsCompact K)
  (hKne : K.Nonempty)
  (hzK : z ∈ K)
  (hmax : l z = suppFunc K l)
  (huniq : ∀ y ∈ K, l y = suppFunc K l → y = z) :
-- imply
  z ∈ K.exposedPoints ℝ := by
-- proof
  apply Convex.Straszewicz.unique_maximizer_exposed hK hKne hzK hmax huniq

/--
[Straszewicz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean)
-/
@[path]
private lemma straszewicz_theorem_le
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : Set E}
  (hA_compact : IsCompact A)
  (hA_convex : Convex ℝ A) :
-- imply
  A.extremePoints ℝ ⊆ closure (A.exposedPoints ℝ) := by
-- proof
  apply Convex.Straszewicz.straszewicz_theorem hA_compact hA_convex

-- created on 2026-10-10
