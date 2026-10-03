/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces
public import RingedSpaces.Modules.SheafInverseImageHom

/-!
# Root-plus-direct-import coexistence client

The root now re-exports the sheaf inverse-image leaves. This client retains its
explicit leaf import to check that it works alongside the public root.
-/

@[expose] public section

open CategoryTheory
open RingedSpaces.Modules.SheafInverseImage

namespace Test.SheafInverseImageRootCoexist

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (S : Y.Sheaf CommRingCat.{v})
  (M : SheafOfModules.{v} (sourceRing S))

theorem wholeUnitWithOldRoot :
    (SheafOfModules.toSheaf (sourceRing S)).map ((adjunction f S).unit.app M) =
      moduleUnit f S M :=
  unit_underlying f S M

end Test.SheafInverseImageRootCoexist
