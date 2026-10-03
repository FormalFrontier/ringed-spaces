/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.RingedSpacePullback

set_option warningAsError true

/-! Historical filename; a native module-system client of the public pullback API. -/

@[expose] public section

open CategoryTheory
open RingedSpaces.Modules.RingedSpacePullback

namespace Test.RingedSpacePullbackLegacy

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Compatibility of the core adjunction through a direct public import. -/
noncomputable def legacyAdjunction :
    pullbackFunctor f ⊣ RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor f :=
  adjunction f

#print axioms legacyAdjunction

end Test.RingedSpacePullbackLegacy

#lint
