/-
SPDX-License-Identifier: Apache-2.0
Authors: formalization-worker-b (Hive Task hive-request-da7e7acee403b485010744c0c39bcd03c2bc1041,
  UID 2978daa3-8653-4a85-b398-56608e5a29e8)
-/
module

public import RingedSpaces

/-! # Clients of constant-closed full ringed-space morphisms -/

set_option warningAsError true

@[expose] public section

namespace Test.ClosedPointHom

open CategoryTheory Opposite TopologicalSpace TopCat AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ClosedPointHom

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] (X : RingedSpace.{u})

noncomputable example (alpha : R →+* X.presheaf.obj (op ⊤)) :
    X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R) := hom R X alpha

example (alpha : R →+* X.presheaf.obj (op ⊤)) (x : X) :
    (hom R X alpha).hom.base x = IsLocalRing.closedPoint R := by
  change base R X x = IsLocalRing.closedPoint R
  rfl

example (alpha : R →+* X.presheaf.obj (op ⊤)) :
    (StructureSheaf.globalSectionsIso (CommRingCat.of R)).hom ≫
        (hom R X alpha).hom.c.app (op ⊤) ≫
          X.presheaf.map (eqToHom (by simp)) = CommRingCat.ofHom alpha :=
  hom_top_transport R X alpha

noncomputable example : (R →+* X.presheaf.obj (op ⊤)) ≃
    { f : X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R) // f.hom.base = base R X } :=
  equiv R X

example {f g : X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R)}
    (hf : f.hom.base = base R X) (hg : g.hom.base = base R X)
    (h : globalSectionsMap R X f = globalSectionsMap R X g) : f = g :=
  ext R X hf hg h

example (Y : RingedSpace.{u}) (g : Y ⟶ X)
    (alpha : R →+* X.presheaf.obj (op ⊤)) :
    g ≫ hom R X alpha =
      hom R Y (CommRingCat.ofHom alpha ≫ g.hom.c.app (op ⊤)).hom :=
  comp_hom R X g alpha

noncomputable example [IsEmpty X] (alpha : R →+* X.presheaf.obj (op ⊤)) :
    X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R) := hom R X alpha

noncomputable example (K : Type u) [Field K] (Y : RingedSpace.{u})
    (alpha : K →+* Y.presheaf.obj (op ⊤)) :
    Y ⟶ Spec.sheafedSpaceObj (CommRingCat.of K) := hom K Y alpha

/-- A ring homomorphism to a field that does not kill a maximal-ideal element yields
a constant-closed ringed morphism different from the affine-induced one. -/
theorem nonlocal_ne_affine {K : Type u} [Field K] (alpha : R →+* K) (r : R)
    (hr : r ∈ IsLocalRing.maximalIdeal R) (hne : alpha r ≠ 0) :
    hom R (Spec.sheafedSpaceObj (CommRingCat.of K))
        (CommRingCat.ofHom alpha ≫
          (StructureSheaf.globalSectionsIso (CommRingCat.of K)).hom).hom ≠
      Spec.sheafedSpaceMap (CommRingCat.ofHom alpha) := by
  intro heq
  have hb : IsLocalRing.closedPoint R =
      PrimeSpectrum.comap alpha (⊥ : PrimeSpectrum K) := by
    have hbase := congrArg
      (fun f : Spec.sheafedSpaceObj (CommRingCat.of K) ⟶
          Spec.sheafedSpaceObj (CommRingCat.of R) => f.hom.base (⊥ : PrimeSpectrum K)) heq
    change IsLocalRing.closedPoint R = PrimeSpectrum.comap alpha (⊥ : PrimeSpectrum K)
      at hbase
    exact hbase
  have hm : r ∈ (PrimeSpectrum.comap alpha (⊥ : PrimeSpectrum K)).asIdeal := by
    rw [← hb]
    exact hr
  apply hne
  simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] using hm

end Test.ClosedPointHom
