/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TMCodingInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.RecursionTheorem
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.RecursionTheorem
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SelfReference
import Def.v1.Atlas.TheoryOfComputation.code.SelfReference.Part7
/-- A fixed binary encoding `⟨·⟩ : ℕ → List Bool` of natural-number TM indices. -/
/-- The standard `TMCoding` instance for `RecursionTheorem`, packaging the
behavior-level encoding, pairing, s-m-n, and computability operations into the
abstract `TMCoding Bool` structure used by the recursion theorem development. -/
/-- The standard `TMCoding` instance for `TuringMachine`, packaging the
language-level data (`languageOf`, language-computability, `enumSearch`, etc.)
into a single coding used by the general TM theory. -/


namespace RecursionTheorem

end RecursionTheorem

namespace TuringMachine

end TuringMachine
