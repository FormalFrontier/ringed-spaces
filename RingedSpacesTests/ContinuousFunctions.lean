/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import RingedSpaces

/-! Ordinary-import examples for continuous-function ringed and locally ringed spaces. -/

set_option warningAsError true

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace ContinuousFunctionsTest

section GeneralRing

variable {X Y Z R : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

example (f : X → Y) (hf : Continuous f) (U : Opens Y)
    (s : (ContinuousFunctions.sheaf Y R).presheaf.obj (Opposite.op U))
    (point : ContinuousFunctions.inverseImage X Y f hf U) :
    ContinuousFunctions.precompose X R Y f hf U s point = s ⟨f point.1, point.2⟩ :=
  ContinuousFunctions.precompose_apply X R Y f hf U s point

example (f : X → Y) (hf : Continuous f) (x : X) :
    (ContinuousFunctions.ringedSpaceMap X R Y f hf).hom.stalkMap x ≫
      ContinuousFunctions.evalHom X R x = ContinuousFunctions.evalHom Y R (f x) :=
  ContinuousFunctions.ringedSpaceMap_stalkMap_evalHom X R Y f hf x

example : ContinuousFunctions.ringedSpaceMap X R X id continuous_id =
    𝟙 (ContinuousFunctions.ringedSpace X R) :=
  ContinuousFunctions.ringedSpaceMap_id X R

example (f : X → Y) (hf : Continuous f) (g : Y → Z) (hg : Continuous g) :
    ContinuousFunctions.ringedSpaceMap X R Z (g ∘ f) (hg.comp hf) =
      ContinuousFunctions.ringedSpaceMap X R Y f hf ≫
        ContinuousFunctions.ringedSpaceMap Y R Z g hg :=
  ContinuousFunctions.ringedSpaceMap_comp X R Y Z f hf g hg

example : ContinuousFunctions.ringedSpaceMap PEmpty R PEmpty id continuous_id =
    𝟙 (ContinuousFunctions.ringedSpace PEmpty R) :=
  ContinuousFunctions.ringedSpaceMap_id PEmpty R

example [Subsingleton R] (f : X → Y) (hf : Continuous f) :
    ContinuousFunctions.ringedSpace X R ⟶ ContinuousFunctions.ringedSpace Y R :=
  ContinuousFunctions.ringedSpaceMap X R Y f hf

end GeneralRing

variable {X Y Z K : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T1Space K]

example (x : X) : Function.Surjective (ContinuousFunctions.eval X K x) :=
  ContinuousFunctions.eval_surjective X K x

example (x : X) (germ : ContinuousFunctions.stalk X K x) :
    IsUnit germ ↔ ContinuousFunctions.eval X K x germ ≠ 0 :=
  ContinuousFunctions.isUnit_stalk_iff X K x germ

example (x : X) : IsLocalRing (ContinuousFunctions.stalk X K x) := inferInstance

example (f : X → Y) (hf : Continuous f) (x : X) :
    (ContinuousFunctions.locallyRingedSpaceMap X K Y f hf).stalkMap x ≫
      ContinuousFunctions.evalHom X K x = ContinuousFunctions.evalHom Y K (f x) :=
  ContinuousFunctions.stalkMap_evalHom X K Y f hf x

example (f : X → Y) (hf : Continuous f) (x : X) :
    IsLocalHom ((ContinuousFunctions.locallyRingedSpaceMap X K Y f hf).stalkMap x).hom :=
  ContinuousFunctions.stalkMap_isLocalHom X K Y f hf x

example (f : X → Y) (hf : Continuous f) :
    LocallyRingedSpace.forgetToSheafedSpace.map
      (ContinuousFunctions.locallyRingedSpaceMap X K Y f hf) =
      ContinuousFunctions.ringedSpaceMap X K Y f hf :=
  ContinuousFunctions.forget_locallyRingedSpaceMap X K Y f hf

example : ContinuousFunctions.locallyRingedSpaceMap X K X id continuous_id =
    𝟙 (ContinuousFunctions.locallyRingedSpace X K) :=
  ContinuousFunctions.locallyRingedSpaceMap_id X K

example (f : X → Y) (hf : Continuous f) (g : Y → Z) (hg : Continuous g) :
    ContinuousFunctions.locallyRingedSpaceMap X K Z (g ∘ f) (hg.comp hf) =
      ContinuousFunctions.locallyRingedSpaceMap X K Y f hf ≫
        ContinuousFunctions.locallyRingedSpaceMap Y K Z g hg :=
  ContinuousFunctions.locallyRingedSpaceMap_comp X K Y Z f hf g hg

end ContinuousFunctionsTest
