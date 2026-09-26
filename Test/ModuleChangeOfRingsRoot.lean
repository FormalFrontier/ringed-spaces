/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Aggregate-import change-of-rings client
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Test.ModuleChangeOfRingsRoot

theorem scalarRestriction (A B : (Fin 2)ᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)
    (M : RingedSpaces.Modules.Presheaves A)
    (b : B.obj (Opposite.op (1 : Fin 2))) (m : M.obj (Opposite.op (1 : Fin 2))) :
    (RingedSpaces.Modules.tensorPresheaf A B theta M).map
        ((homOfLE (by decide : (0 : Fin 2) ≤ 1)).op)
        (b • RingedSpaces.Modules.tensorUnitSection A B theta M (Opposite.op 1) m) =
      B.map ((homOfLE (by decide : (0 : Fin 2) ≤ 1)).op) b •
        RingedSpaces.Modules.tensorUnitSection A B theta M (Opposite.op 0)
          (M.map ((homOfLE (by decide : (0 : Fin 2) ≤ 1)).op) m) := by
  exact RingedSpaces.Modules.tensorRestriction_smul A B theta M
    ((homOfLE (by decide : (0 : Fin 2) ≤ 1)).op) b m

/-- The same-site adjunction inferred from topological sheafification witnesses. -/
noncomputable def topologicalSheafAdjunction {X : TopCat.{u}}
    (A B : TopCat.Sheaf CommRingCat.{u} X) (theta : A ⟶ B) :
    RingedSpaces.Modules.tensorSheafFunctor A B theta ⊣
      SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta) :=
  RingedSpaces.Modules.opensTensorSheafAdjunction A B theta

end Test.ModuleChangeOfRingsRoot
