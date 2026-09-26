/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces
public import RingedSpaces.Modules.RingedSpacePullback

set_option warningAsError true

/-! The public root exports this leaf; the explicit import checks root-plus-direct compatibility. -/

@[expose] public section

open CategoryTheory
open RingedSpaces.Modules.RingedSpacePullback

namespace Test.RingedSpacePullbackRootCoexist

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Explicit import of the leaf works alongside the root that exports it. -/
noncomputable def comparison :
    pullbackFunctor f ≅
      SheafOfModules.pullback (RingedSpaces.Modules.RingedSpacePushforward.structureMap f) :=
  nativeComparison f

end Test.RingedSpacePullbackRootCoexist

#lint
