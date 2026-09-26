/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

import RingedSpaces.Modules.RingedSpacePullback

set_option warningAsError true

/-! Legacy unqualified import works separately from the native public clients. -/

open CategoryTheory
open RingedSpaces.Modules.RingedSpacePullback

namespace Test.RingedSpacePullbackLegacy

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Compatibility of the core adjunction with a legacy import. -/
noncomputable def legacyAdjunction :
    pullbackFunctor f ⊣ RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor f :=
  adjunction f

#print axioms legacyAdjunction

end Test.RingedSpacePullbackLegacy

#lint
