/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.RingedSpacePullback
public import RingedSpacesTests.RingedSpacePushforwardConcrete

set_option warningAsError true

/-!
# Concrete nonidentity, empty-source and zero-ring boundaries

The existing proper-open and full-map fixtures are reused unchanged. These
instances verify the types and formal identities; they do not claim that an
arbitrary sheafified tensor section is a raw tensor or a nonzero section.
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open RingedSpaces.Modules.RingedSpacePullback

namespace Test.RingedSpacePullbackConcrete

open Test.RingedSpacePushforwardConcrete

/-- The coefficient-bearing full map used here is nonidentity on a proper open. -/
theorem properAndNonidentity :
    properOpen ≠ (⊤ : Opens twoPoints) ∧
      (0 : Fin 2) ∈ properOpen ∧ (fullMap primeSheaf).hom.base ≠ 𝟙 twoPoints :=
  Test.RingedSpacePushforwardConcrete.properAndNonidentity

theorem properOpenFullStructure (r : (RingedSpaces.Modules.RingedSpacePushforward.ringSheaf
    (space primeSheaf)).obj.obj (Opposite.op properOpen)) :
    (RingedSpaces.Modules.RingedSpacePushforward.structureMap
      (fullMap primeSheaf)).hom.app (Opposite.op properOpen) r =
        (fullMap primeSheaf).hom.c.app (Opposite.op properOpen) r :=
  RingedSpaces.Modules.RingedSpacePushforward.structureMap_original
    (fullMap primeSheaf) (Opposite.op properOpen) r

/-- Native pullback comparison for a full map with nonidentity continuous base. -/
noncomputable def nonidentityComparison :
    pullbackFunctor (fullMap primeSheaf) ≅
      SheafOfModules.pullback
        (RingedSpaces.Modules.RingedSpacePushforward.structureMap (fullMap primeSheaf)) :=
  nativeComparison (fullMap primeSheaf)

theorem properOpenUnit
    (M : SheafOfModules (RingedSpaces.Modules.RingedSpacePushforward.ringSheaf
      (space primeSheaf))) :
    (adjunction (fullMap primeSheaf)).unit.app M ≫
      (RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor
        (fullMap primeSheaf)).map ((nonidentityComparison).hom.app M) =
      (nativeAdjunction (fullMap primeSheaf)).unit.app M :=
  nativeComparison_unit (fullMap primeSheaf) M

/-- The same comparison in the empty-source boundary case. -/
noncomputable def emptyComparison :
    pullbackFunctor (emptyMap primeSheaf) ≅
      SheafOfModules.pullback
        (RingedSpaces.Modules.RingedSpacePushforward.structureMap (emptyMap primeSheaf)) :=
  nativeComparison (emptyMap primeSheaf)

/-- The adjunction also exists for the zero-ring coefficient fixture. -/
noncomputable def zeroRingAdjunction :
    pullbackFunctor (fullMap zeroSheaf) ⊣
      RingedSpaces.Modules.RingedSpacePushforward.pushforwardFunctor (fullMap zeroSheaf) :=
  adjunction (fullMap zeroSheaf)

end Test.RingedSpacePullbackConcrete

#lint
