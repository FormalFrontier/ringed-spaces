/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.InverseImage
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Direct-import clients for inverse-image ringed spaces

Only public declarations are used for the arbitrary continuous and full-map clients.
The fixtures also exercise identity, empty carrier and the zero ring, including a
nonidentity full map with a constant underlying continuous map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category AlgebraicGeometry TopCat TopologicalSpace

namespace Test.InverseImage

universe u

/-- A continuous map alone determines the literal carrier, ring sheaf and entire unit map. -/
theorem arbitraryContinuous (Y : RingedSpace.{u, u}) {T : TopCat.{u}}
    (g : T ⟶ Y.carrier) :
    (RingedSpace.inverseImage Y g).carrier = T ∧
      (RingedSpace.inverseImage Y g).sheaf =
        (TopCat.Sheaf.pullback CommRingCat.{u} g).obj Y.sheaf ∧
      (RingedSpace.ofInverseImage Y g).hom.base = g ∧
      (RingedSpace.ofInverseImage Y g).hom.c =
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app Y.sheaf).hom :=
  ⟨RingedSpace.inverseImage_carrier Y g, RingedSpace.inverseImage_sheaf Y g,
    RingedSpace.ofInverseImage_base Y g, RingedSpace.ofInverseImage_c Y g⟩

/-- The canonical map's ring homomorphism on each open is the native adjunction unit. -/
theorem unitOnOpen (Y : RingedSpace.{u, u}) {T : TopCat.{u}}
    (g : T ⟶ Y.carrier) (U : (Opens Y.carrier)ᵒᵖ) :
    (RingedSpace.ofInverseImage Y g).hom.c.app U =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app Y.sheaf).hom.app U :=
  RingedSpace.ofInverseImage_c_app Y g U

/-- An arbitrary full morphism has the mate, both base maps and full factorization. -/
theorem arbitraryFull {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (RingedSpace.toInverseImage f).hom.base = 𝟙 (X : TopCat) ∧
      (RingedSpace.ofInverseImage Y f.hom.base).hom.base = f.hom.base ∧
      (RingedSpace.toInverseImage f ≫ RingedSpace.ofInverseImage Y f.hom.base) = f ∧
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
          Y.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          (RingedSpace.inverseImageMap f)).hom = f.hom.c :=
  ⟨RingedSpace.toInverseImage_base f, RingedSpace.ofInverseImage_base Y f.hom.base,
    RingedSpace.toInverseImage_ofInverseImage f, RingedSpace.inverseImageMap_unit_hom f⟩

/-- The ring-sheaf equation, the original presheaf component on every open and
the identity-pushforward transport of the first map. -/
theorem componentOnOpen {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (U : (Opens Y.carrier)ᵒᵖ) (V : (Opens X.carrier)ᵒᵖ) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        (RingedSpace.inverseImageMap f) =
        (CategoryTheory.Sheaf.homEquiv).symm f.hom.c ∧
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
          Y.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          (RingedSpace.inverseImageMap f)).hom).app U = f.hom.c.app U ∧
      (RingedSpace.toInverseImage f).hom.c.app V =
        (RingedSpace.inverseImageMap f).hom.app V ≫
          (eqToHom (TopCat.Presheaf.Pushforward.id_eq X.presheaf).symm).app V :=
  ⟨RingedSpace.inverseImageMap_unit f, RingedSpace.inverseImageMap_unit_app f U,
    RingedSpace.toInverseImage_c_app f V⟩

/-- Explicit ring homomorphisms on each target/source open, with the identity transport erased. -/
theorem sectionMaps {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (U : (Opens Y.carrier)ᵒᵖ) (V : (Opens X.carrier)ᵒᵖ) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
      Y.sheaf).hom.app U ≫
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        (RingedSpace.inverseImageMap f)).hom.app U = f.hom.c.app U ∧
      (RingedSpace.toInverseImage f).hom.c.app V =
        (RingedSpace.inverseImageMap f).hom.app V :=
  ⟨RingedSpace.inverseImageMap_unit_components f U, RingedSpace.toInverseImage_c_app_eq f V⟩

/-- Identity morphisms are covered by the same complete full-morphism theorem. -/
theorem identity (X : RingedSpace.{u, u}) :
    RingedSpace.toInverseImage (𝟙 X) ≫
      RingedSpace.ofInverseImage X (𝟙 X : X ⟶ X).hom.base = 𝟙 X :=
  RingedSpace.toInverseImage_ofInverseImage (𝟙 X)

/-- The factorization also holds with an empty underlying source. -/
theorem emptyCarrier (X : RingedSpace.{u, u}) :
    RingedSpace.toInverseImage (X.ofRestrict (Opens.isOpenEmbedding ⊥)) ≫
      RingedSpace.ofInverseImage X (X.ofRestrict (Opens.isOpenEmbedding ⊥)).hom.base =
        X.ofRestrict (Opens.isOpenEmbedding ⊥) :=
  RingedSpace.toInverseImage_ofInverseImage _

/-- The constant terminal-ring presheaf is a sheaf, including on empty opens. -/
def zeroRingSpace (T : TopCat.{u}) : RingedSpace.{u, u} where
  carrier := T
  presheaf := (Functor.const _).obj (CommRingCat.of.{u} PUnit)
  IsSheaf := CategoryTheory.Presheaf.isSheaf_of_isTerminal
    (Opens.grothendieckTopology T) CommRingCat.punitIsTerminal

/-- Nonzero rings are not needed for a full factorization. -/
theorem zeroRing (T : TopCat.{u}) :
    RingedSpace.toInverseImage (𝟙 (zeroRingSpace T)) ≫
      RingedSpace.ofInverseImage (zeroRingSpace T)
        (𝟙 (zeroRingSpace T) : zeroRingSpace T ⟶ zeroRingSpace T).hom.base =
        𝟙 (zeroRingSpace T) :=
  RingedSpace.toInverseImage_ofInverseImage _

/-- A genuinely nonidentity full map over a constant map of a two-point discrete space. -/
theorem nonidentityFull :
    ∃ (Y : RingedSpace.{0, 0}) (g : Y.carrier ⟶ Y.carrier),
      g ≠ 𝟙 (Y : TopCat) ∧
      (RingedSpace.ofInverseImage Y g).hom.base ≠ 𝟙 (Y : TopCat) ∧
        RingedSpace.toInverseImage (RingedSpace.ofInverseImage Y g) ≫
          RingedSpace.ofInverseImage Y (RingedSpace.ofInverseImage Y g).hom.base =
            RingedSpace.ofInverseImage Y g := by
  let T : TopCat := @TopCat.of (Fin 2) ⊤
  let Y : RingedSpace := zeroRingSpace T
  let g : T ⟶ Y.carrier := TopCat.const (0 : T)
  have nonidentity : g ≠ 𝟙 (Y : TopCat) := by
    intro equality
    have atOne := congrArg (fun map : T ⟶ T => map (1 : T)) equality
    change (0 : Fin 2) = 1 at atOne
    exact (by decide : (0 : Fin 2) ≠ 1) atOne
  refine ⟨Y, g, nonidentity, ?_, RingedSpace.toInverseImage_ofInverseImage _⟩
  intro equality
  exact nonidentity ((RingedSpace.ofInverseImage_base Y g).symm.trans equality)

end Test.InverseImage
