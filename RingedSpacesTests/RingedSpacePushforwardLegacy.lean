/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.RingedSpacePushforward

set_option warningAsError true

/-! Historical filename; a native module-system public-import client. -/

@[expose] public section

open CategoryTheory
open RingedSpaces.Modules.RingedSpacePushforward

namespace Test.RingedSpacePushforwardLegacy

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

theorem legacyCompleteMap :
    RingedSpaces.Modules.SheafInverseImage.actualUnit f.hom.base Y.sheaf ≫
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).map (ringSheafMap f) =
    structureMap f :=
  actualUnit_comp_ringSheafMap f

#print axioms legacyCompleteMap

end Test.RingedSpacePushforwardLegacy

#lint
