<!-- SPDX-License-Identifier: Apache-2.0 -->

# Constant-closed morphisms not induced by any affine ring map

Import `RingedSpaces.ClosedPointNonAffine` directly, or import the aggregate
`RingedSpaces`. Both expose the namespace
`AlgebraicGeometry.RingedSpace.ClosedPointHom` without an incubator dependency.
The extension builds on the full ringed-morphism constructor explained in
[`closed-point-hom.md`](closed-point-hom.md).

Fix `R S : Type u` in the **same Lean universe**, with `[CommRing R]`,
`[IsLocalRing R]`, `[CommRing S]`, `[Nontrivial S]`. Let
`alpha : R →+* S`, `r : R`, `hr : r ∈ IsLocalRing.maximalIdeal R`, and
`hu : IsUnit (alpha r)`. There is no assumption that `alpha` is local.
For **every** `beta : R →+* S`, the theorem
`hom_ne_sheafedSpaceMap_of_isUnit alpha r hr hu beta` asserts:

```lean
ClosedPointHom.hom R (Spec.sheafedSpaceObj (CommRingCat.of S))
    (CommRingCat.ofHom alpha ≫
      (StructureSheaf.globalSectionsIso (CommRingCat.of S)).hom).hom ≠
  Spec.sheafedSpaceMap (CommRingCat.ofHom beta)
```

The constructor on the left produces an **actual full ringed-space morphism**
`Spec S ⟶ Spec R` with constant base map at the closed point of `Spec R`.
The right-hand side is the actual affine-induced full ringed morphism for
`beta`, not merely a comparison of continuous maps. The second theorem,
`not_exists_sheafedSpaceMap_of_isUnit alpha r hr hu`, packages the same
conclusion as `¬ ∃ beta : R →+* S, ... = Spec.sheafedSpaceMap ...`.
In particular, the `beta` is **arbitrary**: it need not equal `alpha` in
the hypotheses. The older `Test.ClosedPointHom.nonlocal_ne_affine` client
compares only with the affine map induced by that *same* `alpha` to a field;
this new library theorem excludes **every** candidate `beta` and works for
any nontrivial commutative codomain `S`, not just a field.

## Proof and scope

Assume equality of the two full morphisms. Their *actual* maps on global
sections then agree. `ClosedPointHom.hom_globalSectionsMap` computes the
left-hand map as `CommRingCat.ofHom alpha` followed by the canonical
`StructureSheaf.globalSectionsIso` of `Spec S`.
`StructureSheaf.toOpen_comp_comap beta ⊤` computes the right-hand map as
`CommRingCat.ofHom beta` followed by that same isomorphism, accounting for
the top-open inverse-image transport. Cancel the isomorphism to **derive**
`alpha = beta` rather than assume it. Nontriviality of `S` supplies a prime
`p : PrimeSpectrum S`. Equality of the underlying base maps then forces
`IsLocalRing.closedPoint R = PrimeSpectrum.comap alpha p`. Thus `r` belongs
to this contraction, whence `alpha r ∈ p.asIdeal`. A unit cannot belong to
a proper prime ideal, contradicting `hu`.

No field, domain, Noetherian or algebraically closed hypothesis on `S` is
needed. The [root-only client](../Test/ClosedPointNonAffine.lean) uses both
arbitrary field `beta` and arbitrary `beta : R →+* K × K` for a non-field
product of fields; it imports **only** the public root. Nontriviality
provides the prime used in the proof; this theorem makes no claim for the
zero ring's empty spectrum. Neither theorem asserts a local map on stalks,
a locally ringed-space/scheme morphism, or a zero-ring conclusion.

## Reproduce

Use the checked-in `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) and
`lakefile.toml` (sole direct dependency mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`). From the repository root:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build RingedSpaces Test.ClosedPointNonAffine
```

Formal Frontier contributors developed the original non-affineness proof and
field/product-of-fields clients, then adapted them for this library with a
root-only client and this guide. See [`NOTICE.md`](../NOTICE.md).
