import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.DickmanDeBruijn


namespace Real

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
lemma IsDickmanDeBruijn.eq_zero_of_neg
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : u < 0) :
-- imply
  ρ u = 0 :=
-- proof
  h.1 u hu

end Real

namespace Real

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
lemma IsDickmanDeBruijn.mapsTo_Ici_Icc
-- given
  (ρ : ℝ → ℝ)
  (h : Real.IsDickmanDeBruijn ρ) :
-- imply
  Set.MapsTo ρ (Set.Ici (0 : ℝ)) (Set.Icc (0 : ℝ) 1) :=
-- proof
  h.2.1

end Real

namespace Real

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
lemma IsDickmanDeBruijn.continuousOn_Ici
-- given
  (ρ : ℝ → ℝ)
  (h : Real.IsDickmanDeBruijn ρ) :
-- imply
  ContinuousOn ρ (Set.Ici (0 : ℝ)) :=
-- proof
  h.2.2.1

end Real

namespace Real

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
lemma IsDickmanDeBruijn.eq_one_of_mem_Icc
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : u ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  ρ u = 1 :=
-- proof
  h.2.2.2.1 u hu

end Real

namespace Real

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
lemma IsDickmanDeBruijn.eq_one_of_nonneg_of_le_one
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (h0 : 0 ≤ u)
  (h1 : u ≤ 1) :
-- imply
  ρ u = 1 :=
-- proof
  h.eq_one_of_mem_Icc ⟨h0, h1⟩

end Real

namespace Real

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
lemma IsDickmanDeBruijn.differentiableAt_of_one_lt
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : 1 < u) :
-- imply
  DifferentiableAt ℝ ρ u :=
-- proof
  (h.2.2.2.2 u hu).1

end Real

namespace Real

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
lemma IsDickmanDeBruijn.delay_eq
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : 1 < u) :
-- imply
  u * deriv ρ u + ρ (u - 1) = 0 :=
-- proof
  (h.2.2.2.2 u hu).2

end Real

namespace Real

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
lemma IsDickmanDeBruijn.nonneg_of_nonneg
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : 0 ≤ u) :
-- imply
  0 ≤ ρ u :=
-- proof
  (h.mapsTo_Ici_Icc hu).1

end Real

namespace Real

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
lemma IsDickmanDeBruijn.le_one_of_nonneg
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : 0 ≤ u) :
-- imply
  ρ u ≤ 1 :=
-- proof
  (h.mapsTo_Ici_Icc hu).2

end Real

namespace Real

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
lemma IsDickmanDeBruijn.mem_Icc_of_nonneg
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : 0 ≤ u) :
-- imply
  ρ u ∈ Set.Icc (0 : ℝ) 1 :=
-- proof
  h.mapsTo_Ici_Icc hu

end Real


-- created on 2026-10-11
-- updated on 2026-10-26
