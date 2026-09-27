<!-- SPDX-License-Identifier: Apache-2.0 -->

# Constant-closed full ringed morphisms

Import `RingedSpaces` or `RingedSpaces.ClosedPointHom` for the namespace
`AlgebraicGeometry.RingedSpace.ClosedPointHom`. Fix `R : Type u` with
`[CommRing R] [IsLocalRing R]` and any `X : RingedSpace.{u}`. Given an arbitrary
unital ring homomorphism `alpha : R →+* X.presheaf.obj (op ⊤)`, `hom R X alpha`
is an **actual full ringed-space morphism**
`X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R)`. Its source need not be affine,
nonempty, Noetherian, a domain or even a locally ringed space. The ring map
need not be local. The compatible universe is required for the displayed
native morphism type; no mixed-universe lift is asserted.

## Construction and computations

`base R X` is constant at `IsLocalRing.closedPoint R`, as `base_apply` and
`hom_base` confirm. The closed point lies in an open of the spectrum of a local
ring exactly when that open is top. Thus `preimage_eq_bot` makes the inverse
image of any proper target open empty. On these opens the genuine sheaf on
`X` has a terminal empty-open component; this gives the unique sheaf-map
components and proves their naturality. At top, `hom` uses the inverse of
`StructureSheaf.globalSectionsIso` followed by `CommRingCat.ofHom alpha`.

`globalSectionsMap R X f` extracts the map on global sections from the actual
top component of any `f : X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R)`.
`hom_globalSectionsMap` computes its value for `hom R X alpha` as
`CommRingCat.ofHom alpha`. `globalSectionsMap_eq_transport` and
`hom_top_transport` state the same computation with the inverse-image-top
transport `X.presheaf.map (eqToHom (by simp))` shown explicitly. At the native
types used here, the transport simplifies to the identity map; the result does
not assert a nondefinitional transport theorem.

`ext R X` says equal global-sections maps determine equal morphisms when both
bases are `base R X`. The equivalence `equiv R X` classifies **all** full
ringed morphisms with this fixed base by `R →+* X.presheaf.obj (op ⊤)`;
both inverse laws are proved. For any full morphism `g : Y ⟶ X`, `comp_hom`
identifies `g ≫ hom R X alpha` with the construction on `Y` using the
composite of `alpha` and the top component of `g`.

## Scope and checked uses

The [root-only client](../Test/ClosedPointHom.lean) exercises arbitrary and
empty sources, field targets, base and top calculations, fixed-base
extensionality and equivalence, and precomposition. Its conditional theorem
`Test.ClosedPointHom.nonlocal_ne_affine` assumes a ring homomorphism to a field
that sends some maximal-ideal element to a nonzero element. It proves that the
resulting constant-closed morphism differs from the affine-induced morphism
for that same ring map. In particular, this API does **not** supply a local
ring-map condition at stalks, a locally ringed morphism, or a scheme morphism.

Original Lean proofs and client: formalization-worker-b, Hive Task
`hive-request-da7e7acee403b485010744c0c39bcd03c2bc1041` (UID
`2978daa3-8653-4a85-b398-56608e5a29e8`). Destination transfer, client
adaptation and this guide: formalization-worker-b, Hive Task
`hive-request-14f43b76fa9cc2cc327d381a1a318a9ba7f9e6bd` (UID
`81854e11-fe00-45db-acf2-d465d2e8248c`). See [attribution](../NOTICE.md).
