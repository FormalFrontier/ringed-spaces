/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.RingedSpacePushforward
public import Mathlib.Data.ZMod.Defs

set_option warningAsError true

/-!
# Proper-open, empty-space and zero-ring clients

The two-point topology is discrete (`⊥`), not indiscrete (`⊤`). These clients
make no nonzero claim about sheafified sections or the coefficient comparison.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaces.Modules.RingedSpacePushforward

namespace Test.RingedSpacePushforwardConcrete

private local instance : TopologicalSpace (Fin 2) := ⊥
private local instance : DiscreteTopology (Fin 2) := discreteTopology_bot (Fin 2)
private local instance : TopologicalSpace PEmpty := ⊥

/-- A discrete two-point topological space. -/
abbrev twoPoints : TopCat := TopCat.of (Fin 2)
/-- The empty topological space. -/
abbrev emptySpace : TopCat := TopCat.of PEmpty
/-- The continuous, nonidentity two-point collapse. -/
def collapse : twoPoints ⟶ twoPoints := TopCat.const (0 : twoPoints)
/-- The unique empty-source map used for an empty-space boundary case. -/
def fromEmpty : emptySpace ⟶ twoPoints := TopCat.const (0 : twoPoints)

/-- The proper singleton open of the discrete two-point space. -/
def properOpen : Opens twoPoints :=
  ⟨{(0 : Fin 2)}, isOpen_discrete _⟩

/-- Sheafification of the constant `ZMod 5` coefficient presheaf. -/
noncomputable def primeSheaf : twoPoints.Sheaf CommRingCat :=
  (presheafToSheaf (Opens.grothendieckTopology twoPoints) CommRingCat).obj
    ((Functor.const _).obj (CommRingCat.of (ZMod 5)))

/-- Sheafification of the constant zero-ring coefficient presheaf. -/
noncomputable def zeroSheaf : twoPoints.Sheaf CommRingCat :=
  (presheafToSheaf (Opens.grothendieckTopology twoPoints) CommRingCat).obj
    ((Functor.const _).obj (CommRingCat.of (ZMod 1)))

/-- A ringed space with a supplied commutative structure sheaf. -/
def space (S : twoPoints.Sheaf CommRingCat) : RingedSpace.{0, 0} where
  carrier := twoPoints
  presheaf := S.obj
  IsSheaf := S.property

/-- An actual full ringed-space map with nonidentity continuous base. -/
noncomputable def fullMap (S : twoPoints.Sheaf CommRingCat) :
    RingedSpace.inverseImage (space S) collapse ⟶ space S :=
  RingedSpace.ofInverseImage (space S) collapse

/-- An actual full ringed-space map from the empty space. -/
noncomputable def emptyMap (S : twoPoints.Sheaf CommRingCat) :
    RingedSpace.inverseImage (space S) fromEmpty ⟶ space S :=
  RingedSpace.ofInverseImage (space S) fromEmpty

theorem properAndNonidentity :
    properOpen ≠ (⊤ : Opens twoPoints) ∧
      (0 : Fin 2) ∈ properOpen ∧ (fullMap primeSheaf).hom.base ≠ 𝟙 twoPoints := by
  refine ⟨?_, ?_, ?_⟩
  · intro equality
    have atOne := congrArg (fun U : Opens twoPoints => (1 : Fin 2) ∈ U) equality
    simp [properOpen] at atOne
  · simp [properOpen]
  · intro equality
    have atOne := congrArg (fun g : twoPoints ⟶ twoPoints => g (1 : twoPoints)) equality
    change (0 : Fin 2) = 1 at atOne
    exact (by decide : (0 : Fin 2) ≠ 1) atOne

theorem properOpenActualMap (r : (ringSheaf (space primeSheaf)).obj.obj (op properOpen)) :
    (structureMap (fullMap primeSheaf)).hom.app (op properOpen) r =
      (fullMap primeSheaf).hom.c.app (op properOpen) r :=
  structureMap_original (fullMap primeSheaf) (op properOpen) r

theorem properOpenFullMate :
    RingedSpaces.Modules.SheafInverseImage.actualUnit
        (fullMap primeSheaf).hom.base (space primeSheaf).sheaf ≫
      (TopCat.Sheaf.pushforward RingCat (fullMap primeSheaf).hom.base).map
        (ringSheafMap (fullMap primeSheaf)) =
      structureMap (fullMap primeSheaf) :=
  actualUnit_comp_ringSheafMap (fullMap primeSheaf)

theorem properOpenForward (M : SheafOfModules (ringSheaf
    (RingedSpace.inverseImage (space primeSheaf) collapse)))
    (m : ((SheafOfModules.restrictScalars (ringSheafMap (fullMap primeSheaf)) ⋙
      RingedSpaces.Modules.SheafInverseImage.pushforwardFunctor
        (fullMap primeSheaf).hom.base (space primeSheaf).sheaf).obj M).val.obj
          (op properOpen)) :
    ((restrictPushforwardIso (fullMap primeSheaf)).hom.app M).val.app (op properOpen) m = m :=
  restrictPushforwardIso_hom_app (fullMap primeSheaf) M (op properOpen) m

theorem emptyTargetOpen (r : (ringSheaf (space primeSheaf)).obj.obj
    (op (⊥ : Opens twoPoints))) :
    (structureMap (emptyMap primeSheaf)).hom.app (op (⊥ : Opens twoPoints)) r =
      (emptyMap primeSheaf).hom.c.app (op (⊥ : Opens twoPoints)) r :=
  structureMap_original (emptyMap primeSheaf) (op (⊥ : Opens twoPoints)) r

theorem zeroRingBoundary :
    (1 : ZMod 1) = 0 ∧
      (RingedSpaces.Modules.SheafInverseImage.actualUnit
          (fullMap zeroSheaf).hom.base (space zeroSheaf).sheaf ≫
        (TopCat.Sheaf.pushforward RingCat (fullMap zeroSheaf).hom.base).map
          (ringSheafMap (fullMap zeroSheaf)) = structureMap (fullMap zeroSheaf)) :=
  ⟨Subsingleton.elim _ _, actualUnit_comp_ringSheafMap (fullMap zeroSheaf)⟩

end Test.RingedSpacePushforwardConcrete

#lint
