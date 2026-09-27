/-
SPDX-License-Identifier: Apache-2.0
Authors: formalization-worker-b (Hive Task hive-request-da7e7acee403b485010744c0c39bcd03c2bc1041,
  UID 2978daa3-8653-4a85-b398-56608e5a29e8)
-/
module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Constant-closed morphisms to a local affine spectrum

A ring map from a local ring to the global sections of any ringed space determines a
full ringed-space morphism with constant underlying map at the closed point.
This morphism does not in general preserve local rings at stalks.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace AlgebraicGeometry.RingedSpace.ClosedPointHom

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] (X : RingedSpace.{u})

/-- The constant map to the unique closed point of a local affine spectrum. -/
def base : (X : TopCat) ⟶ (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat) :=
  TopCat.ofHom ⟨fun _ => IsLocalRing.closedPoint R, continuous_const⟩

@[simp] theorem base_apply (x : X) : base R X x = IsLocalRing.closedPoint R := rfl

/-- Every open not containing the closed point has empty inverse image. -/
theorem preimage_eq_bot (U : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat))
    (hU : U ≠ ⊤) :
    (Opens.map (base R X)).obj U = ⊥ := by
  ext x
  change _ ↔ False
  constructor
  · intro hx
    apply hU
    apply (IsLocalRing.closedPoint_mem_iff U).mp
    change IsLocalRing.closedPoint R ∈ U at hx
    exact hx
  · intro hx
    exact hx.elim

/-- The actual map on global sections of any morphism to the affine spectrum. -/
noncomputable def globalSectionsMap (f : X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R)) :
    CommRingCat.of R ⟶ X.presheaf.obj (op ⊤) :=
  (StructureSheaf.globalSectionsIso (CommRingCat.of R)).hom ≫
    f.hom.c.app (op ⊤)

omit [IsLocalRing R] in
/-- Explicit transport from the inverse image of the top open to the top open itself. -/
theorem globalSectionsMap_eq_transport
    (f : X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R)) :
    globalSectionsMap R X f =
      (StructureSheaf.globalSectionsIso (CommRingCat.of R)).hom ≫
        f.hom.c.app (op ⊤) ≫
          X.presheaf.map (eqToHom (by simp)) := by
  have htransport :
      X.presheaf.map (eqToHom (by simp)) =
        𝟙 (X.presheaf.obj (op ⊤)) := by
    change X.presheaf.map (𝟙 (op ⊤)) = 𝟙 _
    exact X.presheaf.map_id _
  rw [htransport]
  exact (Category.comp_id (globalSectionsMap R X f)).symm

/-- A full ringed-space morphism induced by a map on global sections, with constant closed base. -/
noncomputable def hom (alpha : R →+* X.presheaf.obj (op ⊤)) :
    X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R) where
  hom.base := base R X
  hom.c := {
    app := fun U => by
      by_cases hU : U = op (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat))
      · subst U
        exact (StructureSheaf.globalSectionsIso (CommRingCat.of R)).inv ≫
          CommRingCat.ofHom alpha
      · have hu : unop U ≠ (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat)) := by
          intro heq
          exact hU (by cases U; cases heq; rfl)
        exact (X.sheaf.isTerminalOfEqEmpty (preimage_eq_bot R X (unop U) hu)).from _
    naturality := by
      intro U V i
      by_cases hV : V = op (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat))
      · have hU : U = op (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat)) := by
          apply Opposite.unop_injective
          have hle : (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat)) ≤ unop U := by
            have hv : unop V = ⊤ := congrArg unop hV
            simpa only [hv] using (unop i).le
          exact eq_top_iff.mpr hle
        subst U
        subst V
        have : i = 𝟙 _ := Subsingleton.elim _ _
        subst i
        erw [(Spec.sheafedSpaceObj (CommRingCat.of R)).presheaf.map_id]
        erw [((TopCat.Presheaf.pushforward CommRingCat (base R X)).obj X.presheaf).map_id]
        exact (Category.comp_id _).symm
      · have hv : unop V ≠ (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat)) := by
          intro heq
          exact hV (by cases V; cases heq; rfl)
        apply (X.sheaf.isTerminalOfEqEmpty (preimage_eq_bot R X (unop V) hv)).hom_ext
  }

@[simp] theorem hom_base (alpha : R →+* X.presheaf.obj (op ⊤)) :
    (hom R X alpha).hom.base = base R X := rfl

/-- The top component, using the definitional identity `f ⁻¹' ⊤ = ⊤`. -/
theorem hom_globalSectionsMap (alpha : R →+* X.presheaf.obj (op ⊤)) :
    globalSectionsMap R X (hom R X alpha) = CommRingCat.ofHom alpha := by
  calc
    globalSectionsMap R X (hom R X alpha) =
        (StructureSheaf.globalSectionsIso (CommRingCat.of R)).hom ≫
          ((StructureSheaf.globalSectionsIso (CommRingCat.of R)).inv ≫
            CommRingCat.ofHom alpha) := by
              simp [globalSectionsMap, hom]
    _ = CommRingCat.ofHom alpha :=
      (StructureSheaf.globalSectionsIso (CommRingCat.of R)).hom_inv_id_assoc _

/-- The exact top-component computation with the inverse-image-top transport. -/
theorem hom_top_transport (alpha : R →+* X.presheaf.obj (op ⊤)) :
    (StructureSheaf.globalSectionsIso (CommRingCat.of R)).hom ≫
        (hom R X alpha).hom.c.app (op ⊤) ≫
          X.presheaf.map (eqToHom (by simp)) =
      CommRingCat.ofHom alpha := by
  rw [← globalSectionsMap_eq_transport, hom_globalSectionsMap]

/-- Fixed-constant-base extensionality: the global-section map determines all components. -/
theorem ext {f g : X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R)}
    (hf : f.hom.base = base R X) (hg : g.hom.base = base R X)
    (h : globalSectionsMap R X f = globalSectionsMap R X g) : f = g := by
  apply SheafedSpace.ext f g (hf.trans hg.symm)
  apply NatTrans.ext
  funext U
  by_cases hu : unop U = (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat))
  · have hU : U = op (⊤ : Opens (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat)) := by
      cases U
      cases hu
      rfl
    subst U
    have ht : f.hom.c.app (op ⊤) = g.hom.c.app (op ⊤) := by
      exact (Iso.cancel_iso_hom_left (StructureSheaf.globalSectionsIso (CommRingCat.of R))
        _ _).mp h
    simpa using ht
  · have hpre : (Opens.map g.hom.base).obj (unop U) = ⊥ := by
      rw [hg]
      exact preimage_eq_bot R X (unop U) hu
    apply (X.sheaf.isTerminalOfEqEmpty hpre).hom_ext

/-- Maps on global sections classify full ringed morphisms with the fixed closed base. -/
noncomputable def equiv :
    (R →+* X.presheaf.obj (op ⊤)) ≃
      { f : X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R) // f.hom.base = base R X } where
  toFun alpha := ⟨hom R X alpha, rfl⟩
  invFun f := (globalSectionsMap R X f.1).hom
  left_inv alpha := by
    change (globalSectionsMap R X (hom R X alpha)).hom = alpha
    rw [hom_globalSectionsMap]
    rfl
  right_inv f := by
    apply Subtype.ext
    apply ext R X (hom_base R X _) f.2
    simp only [hom_globalSectionsMap, CommRingCat.ofHom_hom]

/-- The constant-closed construction is natural under precomposition in the source. -/
theorem comp_hom {Y : RingedSpace.{u}} (g : Y ⟶ X)
    (alpha : R →+* X.presheaf.obj (op ⊤)) :
    g ≫ hom R X alpha =
      hom R Y (CommRingCat.ofHom alpha ≫ g.hom.c.app (op ⊤)).hom := by
  apply ext R Y
  · ext y
    rfl
  · rfl
  · change (StructureSheaf.globalSectionsIso (CommRingCat.of R)).hom ≫
        ((hom R X alpha).hom.c.app (op ⊤) ≫ g.hom.c.app (op ⊤)) =
        (StructureSheaf.globalSectionsIso (CommRingCat.of R)).hom ≫
          (hom R Y (CommRingCat.ofHom alpha ≫ g.hom.c.app (op ⊤)).hom).hom.c.app (op ⊤)
    rw [← Category.assoc]
    change globalSectionsMap R X (hom R X alpha) ≫ g.hom.c.app (op ⊤) =
      globalSectionsMap R Y
        (hom R Y (CommRingCat.ofHom alpha ≫ g.hom.c.app (op ⊤)).hom)
    rw [hom_globalSectionsMap, hom_globalSectionsMap]
    rfl

end AlgebraicGeometry.RingedSpace.ClosedPointHom
