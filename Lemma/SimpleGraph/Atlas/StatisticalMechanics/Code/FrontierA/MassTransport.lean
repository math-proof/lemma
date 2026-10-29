import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MassTransport
open MeasureTheory StatMech StatMech.FrontierA


/--
[translate_zero_y_by_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MassTransport.lean)
-/
@[path]
private lemma translate_zero_y_by_neg_eq
  {d : ℕ}
  {y : Site d} :
-- imply
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (-y) g • (0 : Site d) = -y ∧ g • y = 0 := by
-- proof
  apply StatMech.FrontierA.translate_zero_y_by_neg y

/--
[lattice_mass_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MassTransport.lean)
-/
@[path]
private lemma lattice_mass_transport_eq
  {d : ℕ}
  [MulAction (Multiplicative (Site d)) E]
  {mu : Measure (ConfigSpace E)}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
  (F : Site d → Site d → ConfigSpace E → ENNReal)
  (hF : ∀ x y, Measurable (F x y))
  (hdiag : IsDiagonallyInvariantTransport F) :
-- imply
  ∫⁻ omega, ∑' y : Site d, F 0 y omega ∂mu = ∫⁻ omega, ∑' x : Site d, F x 0 omega ∂mu := by
-- proof
  apply StatMech.FrontierA.lattice_mass_transport mu hinv F hF hdiag

/--
[lattice_mass_transport_infinite_receiver_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MassTransport.lean)
-/
@[path]
private lemma lattice_mass_transport_infinite_receiver_null_eq
  {d : ℕ}
  [MulAction (Multiplicative (Site d)) E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
  (F : Site d → Site d → ConfigSpace E → ENNReal)
  (hF : ∀ x y, Measurable (F x y))
  (hdiag : IsDiagonallyInvariantTransport F)
  (hout : ∀ omega, ∑' y : Site d, F 0 y omega ≤ 1) :
-- imply
  mu {omega | ∑' x : Site d, F x 0 omega = ⊤} = 0 := by
-- proof
  apply StatMech.FrontierA.lattice_mass_transport_infinite_receiver_null mu hinv F hF hdiag hout

/--
[lattice_mass_transport_forbidden_event_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MassTransport.lean)
-/
@[path]
private lemma lattice_mass_transport_forbidden_event_null_eq
  {d : ℕ}
  [MulAction (Multiplicative (Site d)) E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {bad : Set (ConfigSpace E)}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
  (F : Site d → Site d → ConfigSpace E → ENNReal)
  (hF : ∀ x y, Measurable (F x y))
  (hdiag : IsDiagonallyInvariantTransport F)
  (hout : ∀ omega, ∑' y : Site d, F 0 y omega ≤ 1)
  (hbad : bad ⊆ {omega | ∑' x : Site d, F x 0 omega = ⊤}) :
-- imply
  mu bad = 0 := by
-- proof
  apply StatMech.FrontierA.lattice_mass_transport_forbidden_event_null mu hinv F hF hdiag hout bad hbad


-- created on 2026-10-23
