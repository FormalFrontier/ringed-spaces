/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces

/-!
# Legacy aggregate ordinary-import reduction

This client imports only the aggregate root and independently reconstructs the
pointwise neighborhood-colimit action without implementation-private names.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace
open RingedSpaces.Modules.PresheafInverseImage

namespace Test.PresheafInverseImageLegacyAggregate

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})
  (M : PresheafOfModules.{v} R) (U : Opens X)

@[instance_reducible] private noncomputable def expectedAction :
    Module
      (((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U))
      (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) := by
  letI : IsFiltered (index f U) :=
    { nonempty := ⟨CostructuredArrow.mk <| (homOfLE (show U ≤ (Opens.map f).obj ⊤ from
        by rw [Opens.map_top]; exact le_top)).op⟩
      cocone_objs i j :=
        ⟨CostructuredArrow.mk <| (homOfLE (show U ≤
            (Opens.map f).obj (unop i.left ⊓ unop j.left) from
            le_inf (leOfHom i.hom.unop) (leOfHom j.hom.unop))).op,
          CostructuredArrow.homMk (homOfLE inf_le_left).op,
          CostructuredArrow.homMk (homOfLE inf_le_right).op, trivial⟩
      cocone_maps := fun {_ _} _ _ => ⟨_, 𝟙 _, by
        apply CostructuredArrow.hom_ext
        apply Subsingleton.elim⟩ }
  letI : InitiallySmall.{v} ((index f U)ᵒᵖ) :=
    InitiallySmall.mk' (𝟭 ((index f U)ᵒᵖ))
  let neighborhood : ((index f U)ᵒᵖ)ᵒᵖ ⥤ (Opens Y)ᵒᵖ :=
    unopUnop (index f U) ⋙ CostructuredArrow.proj (Opens.map f).op (op U)
  let ringDiagram : ((index f U)ᵒᵖ)ᵒᵖ ⥤ RingCat.{v} := neighborhood ⋙ R
  let moduleDiagram : PresheafOfModules.{v} ringDiagram :=
    { obj i := M.obj (neighborhood.obj i)
      map φ := M.map (neighborhood.map φ) }
  let ringComparison : colimit ringDiagram ≅
      ((Opens.map f).op.pointwiseLeftKanExtension R).obj (op U) :=
    Functor.Final.colimitIso (unopUnop (index f U))
      (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R)
  let groupComparison : colimit moduleDiagram.presheaf ≅
      ((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U) :=
    Functor.Final.colimitIso (unopUnop (index f U))
      (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf)
  let hcR := colimit.isColimit ringDiagram
  let hcM := colimit.isColimit moduleDiagram.presheaf
  let nativeModule : Module (colimit ringDiagram : RingCat.{v})
      (colimit moduleDiagram.presheaf : AddCommGrpCat.{v}) :=
    PresheafOfModules.ModuleColimit.instModuleCarrierPtOppositeRingCat hcR hcM
  letI : Module (colimit ringDiagram : RingCat.{v})
      (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (op U)) :=
    AddEquiv.module _ groupComparison.symm.addCommGroupIsoToAddEquiv
  exact Module.compHom _ ringComparison.symm.ringCatIsoToRingEquiv.toRingHom

private theorem ordinaryPointwiseReduction :
    pointwiseModule f R M U = expectedAction f R M U := rfl

end Test.PresheafInverseImageLegacyAggregate
