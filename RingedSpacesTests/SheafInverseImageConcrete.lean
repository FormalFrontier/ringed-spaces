/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.SheafInverseImageHom
public import Mathlib.Data.ZMod.Defs

/-!
# Nonidentity, proper-open, empty and zero-ring inverse-image clients

The topology `⊥` on two points is discrete (`⊤` would be indiscrete). All
section equalities quantify over existing sections; nothing asserts that a
sheafified section or a colimit section is nonzero.
-/

open CategoryTheory Opposite TopologicalSpace
open RingedSpaces.Modules.SheafInverseImage

namespace Test.SheafInverseImageConcrete

private local instance : TopologicalSpace (Fin 2) := ⊥
private local instance : DiscreteTopology (Fin 2) := discreteTopology_bot (Fin 2)
private local instance : TopologicalSpace PEmpty := ⊥

private abbrev twoPoints : TopCat := TopCat.of (Fin 2)
private abbrev emptySpace : TopCat := TopCat.of PEmpty
private def collapse : twoPoints ⟶ twoPoints := TopCat.const (0 : twoPoints)
private def fromEmpty : emptySpace ⟶ twoPoints := TopCat.const (0 : twoPoints)

private def properOpen : Opens (TopCat.of (Fin 2)) :=
  ⟨{(0 : Fin 2)}, isOpen_discrete _⟩

private noncomputable def zeroRingSheaf : twoPoints.Sheaf CommRingCat :=
  (presheafToSheaf (Opens.grothendieckTopology twoPoints) CommRingCat).obj
    ((Functor.const _).obj (CommRingCat.of (ZMod 1)))

theorem properAndNonidentity :
    properOpen ≠ (⊤ : Opens twoPoints) ∧
      (0 : Fin 2) ∈ properOpen ∧ collapse ≠ 𝟙 twoPoints := by
  refine ⟨?_, ?_, ?_⟩
  · intro equality
    have atOne := congrArg (fun U : Opens twoPoints => (1 : Fin 2) ∈ U) equality
    simp [properOpen] at atOne
  · simp [properOpen]
  · intro equality
    have atOne := congrArg (fun g : twoPoints ⟶ twoPoints => g (1 : twoPoints)) equality
    change (0 : Fin 2) = 1 at atOne
    exact (by decide : (0 : Fin 2) ≠ 1) atOne

theorem properOpenRingUnit (S : twoPoints.Sheaf CommRingCat)
    (r : (sourceRing S).obj.obj (op properOpen)) :
    (ringIso collapse S).hom.hom.app ((Opens.map collapse).op.obj (op properOpen))
      ((actualUnit collapse S).hom.app (op properOpen) r) =
    (toSheafify (Opens.grothendieckTopology twoPoints) (pointwiseRing collapse S)).app
      ((Opens.map collapse).op.obj (op properOpen))
      (((Opens.map collapse).op.pointwiseLeftKanExtensionUnit (sourceRing S).obj).app
        (op properOpen) r) :=
  ringUnit_full collapse S (op properOpen) r

theorem emptyOpenRingUnit (S : twoPoints.Sheaf CommRingCat)
    (r : (sourceRing S).obj.obj (op (⊥ : Opens twoPoints))) :
    (ringIso collapse S).hom.hom.app ((Opens.map collapse).op.obj (op (⊥ : Opens twoPoints)))
      ((actualUnit collapse S).hom.app (op (⊥ : Opens twoPoints)) r) =
    (toSheafify (Opens.grothendieckTopology twoPoints) (pointwiseRing collapse S)).app
      ((Opens.map collapse).op.obj (op (⊥ : Opens twoPoints)))
      (((Opens.map collapse).op.pointwiseLeftKanExtensionUnit (sourceRing S).obj).app
        (op (⊥ : Opens twoPoints)) r) :=
  ringUnit_full collapse S (op (⊥ : Opens twoPoints)) r

theorem properOpenAdditiveUnit (S : twoPoints.Sheaf CommRingCat)
    (M : SheafOfModules (sourceRing S)) (m : M.val.obj (op properOpen)) :
    (moduleUnit collapse S M).hom.app (op properOpen) m =
      (toSheafify (Opens.grothendieckTopology twoPoints)
        ((Opens.map collapse).op.pointwiseLeftKanExtension M.val.presheaf)).app
        ((Opens.map collapse).op.obj (op properOpen))
        (((Opens.map collapse).op.pointwiseLeftKanExtensionUnit M.val.presheaf).app
          (op properOpen) m) :=
  moduleUnit_pointwise collapse S M (op properOpen) m

theorem nonidentityAdjunction (S : twoPoints.Sheaf CommRingCat)
    (M : SheafOfModules (sourceRing S))
    (N : SheafOfModules (targetRing collapse S)) :
    (moduleFunctor collapse S).map ((adjunction collapse S).unit.app M) ≫
      (adjunction collapse S).counit.app ((moduleFunctor collapse S).obj M) =
        𝟙 ((moduleFunctor collapse S).obj M) ∧
      (adjunction collapse S).unit.app ((pushforwardFunctor collapse S).obj N) ≫
      (pushforwardFunctor collapse S).map ((adjunction collapse S).counit.app N) =
        𝟙 ((pushforwardFunctor collapse S).obj N) :=
  ⟨left_triangle collapse S M, right_triangle collapse S N⟩

theorem emptySpaceAdjunction (S : twoPoints.Sheaf CommRingCat)
    (M : SheafOfModules (sourceRing S))
    (N : SheafOfModules (targetRing fromEmpty S)) :
    (moduleFunctor fromEmpty S).map ((adjunction fromEmpty S).unit.app M) ≫
      (adjunction fromEmpty S).counit.app ((moduleFunctor fromEmpty S).obj M) =
        𝟙 ((moduleFunctor fromEmpty S).obj M) ∧
      (adjunction fromEmpty S).unit.app ((pushforwardFunctor fromEmpty S).obj N) ≫
      (pushforwardFunctor fromEmpty S).map ((adjunction fromEmpty S).counit.app N) =
        𝟙 ((pushforwardFunctor fromEmpty S).obj N) :=
  ⟨left_triangle fromEmpty S M, right_triangle fromEmpty S N⟩

theorem zeroRingBoundary :
    (1 : ZMod 1) = 0 ∧
      actualUnit collapse zeroRingSheaf ≫
        (TopCat.Sheaf.pushforward RingCat collapse).map (ringIso collapse zeroRingSheaf).hom =
        pointwiseSheafUnit collapse RingCat (sourceRing zeroRingSheaf) :=
  ⟨Subsingleton.elim _ _, ringUnit_iso collapse zeroRingSheaf⟩

end Test.SheafInverseImageConcrete
