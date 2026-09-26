/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

import RingedSpaces.Modules.SheafInverseImageHom

/-!
# Legacy-import client for the native sheaf inverse-image module

Unlike the ordinary native module clients, this file has no `module` command.
-/

open CategoryTheory
open RingedSpaces.Modules.SheafInverseImage

namespace Test.SheafInverseImageLegacy

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (S : Y.Sheaf CommRingCat.{v})
  (M : SheafOfModules.{v} (sourceRing S))

theorem legacyWholeUnit :
    (SheafOfModules.toSheaf (sourceRing S)).map ((adjunction f S).unit.app M) =
      moduleUnit f S M :=
  unit_underlying f S M

#print axioms legacyWholeUnit

end Test.SheafInverseImageLegacy
