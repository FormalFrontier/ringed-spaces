/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces
public import RingedSpaces.Modules.RingedSpacePushforward

set_option warningAsError true

/-!
# Root-plus-direct pushforward compatibility

This checks simultaneous imports; the root now exports the pushforward leaf.
-/

@[expose] public section

open CategoryTheory
open RingedSpaces.Modules.RingedSpacePushforward

namespace Test.RingedSpacePushforwardRootCoexist

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

theorem fullMap :
    RingedSpaces.Modules.SheafInverseImage.actualUnit f.hom.base Y.sheaf ≫
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).map (ringSheafMap f) =
    structureMap f :=
  actualUnit_comp_ringSheafMap f

end Test.RingedSpacePushforwardRootCoexist

#lint
