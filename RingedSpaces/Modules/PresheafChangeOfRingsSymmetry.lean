/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.PresheafChangeOfRings
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Right-factor order for presheaf extension of scalars

The section tensor is genuinely `M(U) ⊗[A(U)] B(U)`, with the `A(U)` action
on `B(U)` induced by the component of the ring-presheaf morphism. Tensor
symmetry transports the `B(U)` action and intertwines all restrictions.
-/

@[expose] public section

open CategoryTheory
open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C]
  (A B : Cᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)

/-- The actual `A(U)`-module `B(U)` obtained by restriction along `theta_U`. -/
noncomputable abbrev rightFactor (U : Cᵒᵖ) :
    ModuleCat.{u} ((ringPresheaf A).obj U) := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  exact (ModuleCat.restrictScalars ((ringMap A B theta).app U).hom).obj
    (ModuleCat.of ((ringPresheaf B).obj U) ((ringPresheaf B).obj U))

/-- The genuine `M(U) ⊗[A(U), theta_U] B(U)` in its original factor order. -/
noncomputable def rightSection (M : Presheaves A) (U : Cᵒᵖ) :
    ModuleCat.{u} (A.obj U) := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  letI : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  letI : Module (A.obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  exact ModuleCat.of _ (TensorProduct (A.obj U) (M.obj U)
    (rightFactor A B theta U))

/-- Tensor symmetry as an equivalence of the underlying additive groups. -/
noncomputable def rightSectionAddEquiv (M : Presheaves A) (U : Cᵒᵖ) :
    rightSection A B theta M U ≃+ tensorSection A B theta M U := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  letI : Module ((ringPresheaf A).obj U) (M.obj U) := (M.obj U).isModule
  letI : Module ((ringPresheaf A).obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  exact (TensorProduct.comm ((ringPresheaf A).obj U)
    (M.obj U) (rightFactor A B theta U)).toAddEquiv

/-- Transport the native `B(U)`-module structure onto the right-order tensor. -/
noncomputable abbrev rightModule (M : Presheaves A) (U : Cᵒᵖ) :
    Module ((ringPresheaf B).obj U) (rightSection A B theta M U) :=
  (rightSectionAddEquiv A B theta M U).module _

/-- The right-order tensor as a bundled `B(U)`-module. -/
noncomputable def rightSectionCat (M : Presheaves A) (U : Cᵒᵖ) :
    ModuleCat.{u} ((ringPresheaf B).obj U) :=
  letI := rightModule A B theta M U
  ModuleCat.of _ (rightSection A B theta M U)

/-- Tensor symmetry, linear for the transported action of `B(U)`. -/
noncomputable def rightSectionIso (M : Presheaves A) (U : Cᵒᵖ) :
    rightSectionCat A B theta M U ≅ tensorSection A B theta M U := by
  letI := rightModule A B theta M U
  exact LinearEquiv.toModuleIso ((rightSectionAddEquiv A B theta M U).linearEquiv _)

/-- The original-order generator `m ⊗ b` for arbitrary `b`. -/
noncomputable def rightPure (M : Presheaves A) (U : Cᵒᵖ)
    (m : M.obj U) (b : B.obj U) : rightSectionCat A B theta M U := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  letI : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  letI : Module (A.obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  letI := rightModule A B theta M U
  exact TensorProduct.tmul (A.obj U) m b

/-- The opposite-order generator `b ⊗ m` in the accepted extension. -/
noncomputable def leftPure (M : Presheaves A) (U : Cᵒᵖ)
    (b : B.obj U) (m : M.obj U) : tensorSection A B theta M U := by
  letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  letI : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  letI : Module (A.obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  exact TensorProduct.tmul (A.obj U) b m

theorem rightSectionIso_pure (M : Presheaves A) (U : Cᵒᵖ)
    (m : M.obj U) (b : B.obj U) :
    (rightSectionIso A B theta M U).hom (rightPure A B theta M U m b) =
      leftPure A B theta M U b m := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  let : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  let : Module (A.obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  let : Module (A.obj U) (B.obj U) :=
    (rightFactor A B theta U).isModule
  change (TensorProduct.comm (A.obj U) (M.obj U) (rightFactor A B theta U))
      (TensorProduct.tmul (A.obj U) m b) = TensorProduct.tmul (A.obj U) b m
  exact TensorProduct.comm_tmul (A.obj U) (M.obj U)
    (rightFactor A B theta U) m b

theorem rightSectionIso_inv_tmul (M : Presheaves A) (U : Cᵒᵖ)
    (m : M.obj U) (b : B.obj U) :
    (rightSectionIso A B theta M U).inv
        (leftPure A B theta M U b m) =
      rightPure A B theta M U m b := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  let : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  let : Module (A.obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  let : Module (A.obj U) (B.obj U) :=
    (rightFactor A B theta U).isModule
  change (TensorProduct.comm (A.obj U) (M.obj U) (rightFactor A B theta U)).symm
      (TensorProduct.tmul (A.obj U) b m) = TensorProduct.tmul (A.obj U) m b
  exact TensorProduct.comm_symm_tmul (A.obj U) (M.obj U)
    (rightFactor A B theta U) m b

/-- Explicit scalar action from `rightModule`, without a global instance. -/
noncomputable def rightSectionSmul (M : Presheaves A) (U : Cᵒᵖ)
    (c : B.obj U) (t : rightSectionCat A B theta M U) :
    rightSectionCat A B theta M U :=
  (rightModule A B theta M U).smul c t

theorem smul_pure (M : Presheaves A) (U : Cᵒᵖ)
    (m : M.obj U) (b c : B.obj U) :
    rightSectionSmul A B theta M U c (rightPure A B theta M U m b) =
      rightPure A B theta M U m (c * b) := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  let := rightModule A B theta M U
  let : Module (B.obj U) (rightSectionCat A B theta M U) :=
    rightModule A B theta M U
  let : Module (B.obj U) (tensorSection A B theta M U) :=
    (tensorSection A B theta M U).isModule
  change c • rightPure A B theta M U m b = rightPure A B theta M U m (c * b)
  apply (rightSectionIso A B theta M U).toLinearEquiv.injective
  rw [map_smul]
  simp only [Iso.toLinearEquiv_apply, rightSectionIso_pure]
  exact ModuleCat.ExtendScalars.smul_tmul _ c b m

theorem rightASmul_pure (M : Presheaves A) (U : Cᵒᵖ)
    (a : A.obj U) (m : M.obj U) (b : B.obj U) :
    (rightSection A B theta M U).isModule.smul a (rightPure A B theta M U m b) =
      rightPure A B theta M U ((M.obj U).isModule.smul a m) b := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  let : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  let : Module (A.obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  let : Module (A.obj U) (B.obj U) :=
    (rightFactor A B theta U).isModule
  let : Module (A.obj U) (rightSection A B theta M U) :=
    (rightSection A B theta M U).isModule
  change a • TensorProduct.tmul (A.obj U) m b =
    TensorProduct.tmul (A.obj U) (a • m) b
  exact TensorProduct.smul_tmul' a m b

theorem rightBalance_pure (M : Presheaves A) (U : Cᵒᵖ)
    (a : A.obj U) (m : M.obj U) (b : B.obj U) :
    rightPure A B theta M U ((M.obj U).isModule.smul a m) b =
      rightPure A B theta M U m ((theta.app U).hom a * b) := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  let : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  let : Module (A.obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  let : Module (A.obj U) (B.obj U) :=
    (rightFactor A B theta U).isModule
  change TensorProduct.tmul (A.obj U) (a • m) b =
    TensorProduct.tmul (A.obj U) m ((theta.app U).hom a * b)
  exact TensorProduct.smul_tmul a m b

theorem theta_smul_pure (M : Presheaves A) (U : Cᵒᵖ)
    (a : A.obj U) (m : M.obj U) (b : B.obj U) :
    (rightSection A B theta M U).isModule.smul a (rightPure A B theta M U m b) =
      rightSectionSmul A B theta M U ((theta.app U).hom a)
        (rightPure A B theta M U m b) := by
  rw [rightASmul_pure, rightBalance_pure, smul_pure]

/-- The native tensor `A(U)`-action is the restriction of its transported `B(U)`-action
on every tensor, not only on pure tensors. -/
theorem theta_smul (M : Presheaves A) (U : Cᵒᵖ)
    (a : A.obj U) (t : rightSectionCat A B theta M U) :
    (rightSection A B theta M U).isModule.smul a t =
      rightSectionSmul A B theta M U ((theta.app U).hom a) t := by
  let : CommRing (A.obj U) := inferInstance
  let : CommRing (B.obj U) := inferInstance
  let : Module (A.obj U) (M.obj U) := (M.obj U).isModule
  let : Module (A.obj U) (rightFactor A B theta U) :=
    (rightFactor A B theta U).isModule
  let : Module (A.obj U) (rightSection A B theta M U) :=
    (rightSection A B theta M U).isModule
  let : Module (A.obj U) (rightSectionCat A B theta M U) :=
    (rightSection A B theta M U).isModule
  let : Module (B.obj U) (rightSection A B theta M U) := rightModule A B theta M U
  let : Module (B.obj U)
      (TensorProduct (A.obj U) (M.obj U) (rightFactor A B theta U)) :=
    rightModule A B theta M U
  let : Module (B.obj U) (rightSectionCat A B theta M U) := rightModule A B theta M U
  change a • t = (theta.app U).hom a • t
  induction t using TensorProduct.inductionOn with
  | tmul m b => exact theta_smul_pure A B theta M U a m b
  | add x y hx hy =>
      calc
        a • (x + y) = a • x + a • y := smul_add a x y
        _ = (theta.app U).hom a • x + (theta.app U).hom a • y :=
          congrArg₂ (· + ·) hx hy
        _ = (theta.app U).hom a • (x + y) := (smul_add _ x y).symm

theorem unit_eq_leftPure (M : Presheaves A) (U : Cᵒᵖ)
    (m : M.obj U) :
    tensorUnitSection A B theta M U m = leftPure A B theta M U 1 m := by
  rfl

theorem leftPure_eq_smul_unit (M : Presheaves A) (U : Cᵒᵖ)
    (m : M.obj U) (b : B.obj U) :
    leftPure A B theta M U b m =
      (tensorSection A B theta M U).isModule.smul b
        (tensorUnitSection A B theta M U m) := by
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  let : Module (B.obj U) (tensorSection A B theta M U) :=
    (tensorSection A B theta M U).isModule
  let : Module (B.obj U) (rightSectionCat A B theta M U) :=
    rightModule A B theta M U
  have h := congrArg
    (fun t : rightSectionCat A B theta M U => (rightSectionIso A B theta M U).hom t)
    (smul_pure A B theta M U m 1 b)
  rw [mul_one] at h
  change (rightSectionIso A B theta M U).hom
    (b • rightPure A B theta M U m 1) =
      (rightSectionIso A B theta M U).hom (rightPure A B theta M U m b) at h
  rw [map_smul, rightSectionIso_pure, rightSectionIso_pure] at h
  rw [unit_eq_leftPure]
  change leftPure A B theta M U b m = b • leftPure A B theta M U 1 m
  exact h.symm

/-- The original-order restriction, linear after restricting scalars through `B(f)`. -/
noncomputable def rightRestriction (M : Presheaves A)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    rightSectionCat A B theta M U ⟶
      (ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).obj
        (rightSectionCat A B theta M V) :=
  (rightSectionIso A B theta M U).hom ≫ tensorRestriction A B theta M f ≫
    (ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).map
      (rightSectionIso A B theta M V).inv

theorem rightRestriction_comm (M : Presheaves A) {U V : Cᵒᵖ}
    (f : U ⟶ V) :
    (rightSectionIso A B theta M U).hom ≫ tensorRestriction A B theta M f =
      rightRestriction A B theta M f ≫
        (ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).map
          (rightSectionIso A B theta M V).hom := by
  simp [rightRestriction, Category.assoc]

theorem oppositeRestriction_pure (M : Presheaves A) {U V : Cᵒᵖ}
    (f : U ⟶ V) (m : M.obj U) (b : B.obj U) :
    tensorRestriction A B theta M f (leftPure A B theta M U b m) =
      leftPure A B theta M V ((B.map f).hom b) (M.map f m) := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  let : CommRing ((ringPresheaf B).obj V) := inferInstanceAs (CommRing (B.obj V))
  let : Module (B.obj U) (tensorSection A B theta M U) :=
    (tensorSection A B theta M U).isModule
  let : Module (B.obj V) (tensorSection A B theta M V) :=
    (tensorSection A B theta M V).isModule
  let : Module (B.obj U)
      ((ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).obj
        (tensorSection A B theta M V)) :=
    ((ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).obj
      (tensorSection A B theta M V)).isModule
  rw [leftPure_eq_smul_unit]
  change (tensorRestriction A B theta M f).hom
    ((tensorSection A B theta M U).isModule.smul b
      (tensorUnitSection A B theta M U m)) = _
  have h := (tensorRestriction A B theta M f).hom.map_smul b
    (tensorUnitSection A B theta M U m)
  refine h.trans ?_
  rw [tensorRestriction_unit]
  symm
  refine (leftPure_eq_smul_unit A B theta M V (M.map f m)
    ((B.map f).hom b)).trans ?_
  rfl

theorem rightRestriction_pure (M : Presheaves A) {U V : Cᵒᵖ}
    (f : U ⟶ V) (m : M.obj U) (b : B.obj U) :
    rightRestriction A B theta M f (rightPure A B theta M U m b) =
      rightPure A B theta M V (M.map f m) ((B.map f).hom b) := by
  rw [← rightSectionIso_inv_tmul A B theta M V (M.map f m) ((B.map f).hom b)]
  change (rightSectionIso A B theta M V).inv
    (tensorRestriction A B theta M f
      ((rightSectionIso A B theta M U).hom (rightPure A B theta M U m b))) = _
  rw [rightSectionIso_pure, oppositeRestriction_pure]

theorem rightRestriction_semilinear (M : Presheaves A) {U V : Cᵒᵖ}
    (f : U ⟶ V) (c : B.obj U) (t : rightSectionCat A B theta M U) :
    rightRestriction A B theta M f (rightSectionSmul A B theta M U c t) =
      rightSectionSmul A B theta M V ((B.map f).hom c)
        (rightRestriction A B theta M f t) := by
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  let : CommRing ((ringPresheaf B).obj V) := inferInstanceAs (CommRing (B.obj V))
  let : Module (B.obj U) (rightSectionCat A B theta M U) :=
    rightModule A B theta M U
  let : Module (B.obj V) (rightSectionCat A B theta M V) :=
    rightModule A B theta M V
  let : Module (B.obj U)
      ((ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).obj
        (rightSectionCat A B theta M V)) :=
    ((ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).obj
      (rightSectionCat A B theta M V)).isModule
  have h := (rightRestriction A B theta M f).hom.map_smul c t
  exact h

/-- Actual right-order section tensors and semilinear restrictions form a presheaf. -/
noncomputable def rightPresheaf (M : Presheaves A) :
    Presheaves B :=
  PresheafOfModulesOfCommRing.mk (fun U => rightSectionCat A B theta M U)
    (fun f => rightRestriction A B theta M f)
    (map_id := by
      intro U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      change (rightSectionIso A B theta M U).inv
        (tensorRestriction A B theta M (𝟙 U)
          ((rightSectionIso A B theta M U).hom t)) = t
      have h := congrArg
        (fun k => k ((rightSectionIso A B theta M U).hom t))
        ((tensorPresheaf A B theta M).map_id U)
      change tensorRestriction A B theta M (𝟙 U) ((rightSectionIso A B theta M U).hom t) =
        (rightSectionIso A B theta M U).hom t at h
      rw [h]
      exact (rightSectionIso A B theta M U).hom_inv_id_apply t)
    (map_comp := by
      intro U V W f g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      change (rightSectionIso A B theta M W).inv
          (tensorRestriction A B theta M (f ≫ g)
            ((rightSectionIso A B theta M U).hom t)) =
        (rightSectionIso A B theta M W).inv
          (tensorRestriction A B theta M g
            ((rightSectionIso A B theta M V).hom
              ((rightSectionIso A B theta M V).inv
                (tensorRestriction A B theta M f
                  ((rightSectionIso A B theta M U).hom t)))))
      exact (congrArg (fun x => (rightSectionIso A B theta M W).inv x)
        ((tensorPresheaf A B theta M).map_comp_apply f g
          ((rightSectionIso A B theta M U).hom t))).trans
        (congrArg (fun x => (rightSectionIso A B theta M W).inv
          (tensorRestriction A B theta M g x))
          ((rightSectionIso A B theta M V).inv_hom_id_apply
            (tensorRestriction A B theta M f
              ((rightSectionIso A B theta M U).hom t))).symm))

/-- The right-order presheaf is naturally equivalent to the accepted one. -/
noncomputable def rightPresheafIso (M : Presheaves A) :
    rightPresheaf A B theta M ≅ tensorPresheaf A B theta M :=
  PresheafOfModulesOfCommRing.isoMk (fun U => rightSectionIso A B theta M U)
    (fun _ _ f => (rightRestriction_comm A B theta M f).symm)

/-- Sectionwise tensoring of an `A`-module sheaf morphism, in right order. -/
noncomputable def rightPresheafMap {M N : Presheaves A} (h : M ⟶ N) :
    rightPresheaf A B theta M ⟶ rightPresheaf A B theta N :=
  (rightPresheafIso A B theta M).hom ≫ tensorPresheafMap A B theta h ≫
    (rightPresheafIso A B theta N).inv

theorem oppositeMap_pure {M N : Presheaves A} (h : M ⟶ N) (U : Cᵒᵖ)
    (m : M.obj U) (b : B.obj U) :
    tensorSectionMap A B theta h U (leftPure A B theta M U b m) =
      leftPure A B theta N U b (h.app U m) := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  let : Module (B.obj U) (tensorSection A B theta M U) :=
    (tensorSection A B theta M U).isModule
  let : Module (B.obj U) (tensorSection A B theta N U) :=
    (tensorSection A B theta N U).isModule
  rw [leftPure_eq_smul_unit]
  have hsmul := (tensorSectionMap A B theta h U).hom.map_smul b
    (tensorUnitSection A B theta M U m)
  refine hsmul.trans ?_
  rw [tensorSectionMap_unit]
  exact (leftPure_eq_smul_unit A B theta N U (h.app U m) b).symm

/-- The right-order component of `rightPresheafMap` on one open. -/
noncomputable def rightSectionMap {M N : Presheaves A} (h : M ⟶ N)
    (U : Cᵒᵖ) :
    rightSectionCat A B theta M U ⟶ rightSectionCat A B theta N U :=
  (rightSectionIso A B theta M U).hom ≫ tensorSectionMap A B theta h U ≫
    (rightSectionIso A B theta N U).inv

theorem rightSectionMap_pure {M N : Presheaves A} (h : M ⟶ N)
    (U : Cᵒᵖ) (m : M.obj U) (b : B.obj U) :
    rightSectionMap A B theta h U (rightPure A B theta M U m b) =
      rightPure A B theta N U (h.app U m) b := by
  rw [← rightSectionIso_inv_tmul A B theta N U (h.app U m) b]
  change (rightSectionIso A B theta N U).inv
    (tensorSectionMap A B theta h U
      ((rightSectionIso A B theta M U).hom (rightPure A B theta M U m b))) = _
  rw [rightSectionIso_pure, oppositeMap_pure]

theorem rightPresheafMap_pure {M N : Presheaves A} (h : M ⟶ N)
    (U : Cᵒᵖ) (m : M.obj U) (b : B.obj U) :
    (rightPresheafMap A B theta h).app U (rightPure A B theta M U m b) =
      rightPure A B theta N U (h.app U m) b := by
  exact rightSectionMap_pure A B theta h U m b

theorem rightPresheafMap_restriction {M N : Presheaves A} (h : M ⟶ N)
    {U V : Cᵒᵖ} (f : U ⟶ V) (t : rightSectionCat A B theta M U) :
    rightRestriction A B theta N f (rightSectionMap A B theta h U t) =
      rightSectionMap A B theta h V (rightRestriction A B theta M f t) :=
  (PresheafOfModules.naturality_apply (rightPresheafMap A B theta h) f t).symm

/-- The sectionwise right-order unit, linear over `A(U)`. -/
noncomputable def rightUnitSection (M : Presheaves A) (U : Cᵒᵖ) :
    M.obj U ⟶
      (ModuleCat.restrictScalars ((ringMap A B theta).app U).hom).obj
        (rightSectionCat A B theta M U) :=
  tensorUnitSection A B theta M U ≫
    (ModuleCat.restrictScalars ((ringMap A B theta).app U).hom).map
      (rightSectionIso A B theta M U).inv

theorem rightUnitSection_pure (M : Presheaves A) (U : Cᵒᵖ)
    (m : M.obj U) :
    rightUnitSection A B theta M U m = rightPure A B theta M U m 1 := by
  rw [← rightSectionIso_inv_tmul A B theta M U m 1]
  change (rightSectionIso A B theta M U).inv (tensorUnitSection A B theta M U m) = _
  rw [unit_eq_leftPure]

/-- The compatible presheaf unit `m ↦ m ⊗ 1`. -/
noncomputable def rightPresheafUnit (M : Presheaves A) :
    M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj
      (rightPresheaf A B theta M) :=
  presheafTensorUnit A B theta M ≫
    (PresheafOfModules.restrictScalars (ringMap A B theta)).map
      (rightPresheafIso A B theta M).inv

theorem rightPresheafUnit_pure (M : Presheaves A) (U : Cᵒᵖ)
    (m : M.obj U) :
    (rightPresheafUnit A B theta M).app U m = rightPure A B theta M U m 1 := by
  exact rightUnitSection_pure A B theta M U m

private theorem conjugateId {C : Type*} [Category C] {P Q : C} (i : P ≅ Q) :
    i.hom ≫ 𝟙 Q ≫ i.inv = 𝟙 P := by
  simp

private theorem conjugateComp {C : Type*} [Category C]
    {P Q R P' Q' R' : C} (iP : P ≅ P') (iQ : Q ≅ Q') (iR : R ≅ R')
    (h : P' ⟶ Q') (k : Q' ⟶ R') :
    iP.hom ≫ (h ≫ k) ≫ iR.inv =
      (iP.hom ≫ h ≫ iQ.inv) ≫ (iQ.hom ≫ k ≫ iR.inv) := by
  simp [Category.assoc]

/-- Functoriality in the `A`-module presheaf input. -/
noncomputable def rightPresheafFunctor :
    Presheaves A ⥤ Presheaves B where
  obj := rightPresheaf A B theta
  map h := rightPresheafMap A B theta h
  map_id M := by
    change (rightPresheafIso A B theta M).hom ≫
      (tensorPresheafFunctor A B theta).map (𝟙 M) ≫
      (rightPresheafIso A B theta M).inv = 𝟙 _
    exact (congrArg (fun k => (rightPresheafIso A B theta M).hom ≫ k ≫
      (rightPresheafIso A B theta M).inv)
      ((tensorPresheafFunctor A B theta).map_id M)).trans
        (conjugateId (rightPresheafIso A B theta M))
  map_comp h k := by
    change (rightPresheafIso A B theta _).hom ≫
      (tensorPresheafFunctor A B theta).map (h ≫ k) ≫
      (rightPresheafIso A B theta _).inv =
      ((rightPresheafIso A B theta _).hom ≫
        (tensorPresheafFunctor A B theta).map h ≫
        (rightPresheafIso A B theta _).inv) ≫
      ((rightPresheafIso A B theta _).hom ≫
        (tensorPresheafFunctor A B theta).map k ≫
        (rightPresheafIso A B theta _).inv)
    refine (congrArg (fun q => (rightPresheafIso A B theta _).hom ≫ q ≫
      (rightPresheafIso A B theta _).inv)
      ((tensorPresheafFunctor A B theta).map_comp h k)).trans ?_
    exact conjugateComp (rightPresheafIso A B theta _) (rightPresheafIso A B theta _)
      (rightPresheafIso A B theta _) ((tensorPresheafFunctor A B theta).map h)
      ((tensorPresheafFunctor A B theta).map k)

/-- The natural presheaf-level tensor symmetry, including module-map naturality. -/
noncomputable def rightPresheafNatIso :
    rightPresheafFunctor A B theta ≅ tensorPresheafFunctor A B theta :=
  NatIso.ofComponents (fun M => rightPresheafIso A B theta M) (by
    intro M N h
    change rightPresheafMap A B theta h ≫ (rightPresheafIso A B theta N).hom =
      (rightPresheafIso A B theta M).hom ≫ tensorPresheafMap A B theta h
    simp only [rightPresheafMap, Category.assoc, Iso.inv_hom_id,
      Category.comp_id])

end RingedSpaces.Modules

#lint-
