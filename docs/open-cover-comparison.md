# Comparing morphisms glued on different open covers

Two families of local maps need not use the same cover to define the same
ringed-space morphism. Compare them on every intersection of a member of the
first cover with a member of the second. The existing restriction and gluing
APIs then reduce the question to `OpenCover.hom_ext`.

The declarations below belong to this library's
`AlgebraicGeometry.RingedSpace` namespace. They are in
[`Restriction.lean`](../RingedSpaces/Restriction.lean) and
[`OpenCover.lean`](../RingedSpaces/OpenCover.lean), built on Mathlib's
sheafed-space machinery. The comparison is a mathematical application of
these APIs, not an additional named two-cover theorem or a Lean code example.

## The data and the comparison

Fix `X Y : RingedSpace.{u, u}` and two covers `C D : OpenCover X`.
Their index types `C.J` and `D.J` are both `Type u`. Write
`Uᵢ = C.U i` and `Vⱼ = D.U j`. Suppose we have full morphisms

- `fᵢ : C.obj i ⟶ Y` on the first cover;
- `gⱼ : D.obj j ⟶ Y` on the second cover.

Each family must separately satisfy the pullback-compatibility equations
required by `glueMorphisms`; call these hypotheses `hf` and `hg`.
No agreement between the two families is assumed. If within-cover compatibility
is instead given on literal open intersections,
`pullback_compatibility_iff_intersection` converts it to the required form.
The resulting global maps are

- `F = C.glueMorphisms f hf : X ⟶ Y`;
- `G = D.glueMorphisms g hg : X ⟶ Y`.

For each pair `(i, j)`, put `Wᵢⱼ = Uᵢ ⊓ Vⱼ`. The restriction maps

- `aᵢⱼ = restrictMap Wᵢⱼ Uᵢ inf_le_left`;
- `bᵢⱼ = restrictMap Wᵢⱼ Vⱼ inf_le_right`

both start at the **same literal ringed space**
`X.restrict Wᵢⱼ.isOpenEmbedding`. They map to `C.obj i` and `D.obj j`,
respectively. With `≫` denoting composition in application order, the
comparison is

```text
F = G  if and only if  for every i and j, aᵢⱼ ≫ fᵢ = bᵢⱼ ≫ gⱼ.
```

Both sides of each local equality have the indicated common source and target
`Y`. These are equalities of **full ringed-space morphisms**, including their
structure-sheaf maps. Equality of underlying continuous maps alone does not
supply the required hypothesis.

## Why the existing API suffices

Use an open cover `E` whose index type is `C.J × D.J` and whose member at
`(i, j)` is `Wᵢⱼ`. It covers `X`: a point belongs to some member of `C` and to
some member of `D`, hence to their intersection. This is cover data for the
existing `OpenCover` structure, not a separate public refinement construction.

The two restriction triangles are instances of `restrictMap_ofRestrict`:

```text
aᵢⱼ ≫ C.ι i = E.ι (i, j),
bᵢⱼ ≫ D.ι j = E.ι (i, j).
```

Combine these triangles with associativity and the local equations
`C.ι i ≫ F = fᵢ` and `D.ι j ≫ G = gⱼ`, supplied by `ι_glueMorphisms`.
They give

```text
E.ι (i, j) ≫ F = aᵢⱼ ≫ fᵢ,
E.ι (i, j) ≫ G = bᵢⱼ ≫ gⱼ.
```

Thus the cross-intersection equalities are exactly the hypotheses of
`E.hom_ext F G`, which yields `F = G`. Conversely, equality of the global maps
implies equality after each restriction, and the same two equations give the
local equalities. No identification of a categorical pullback object with a
literal intersection is needed for this calculation, nor does the caller need
to unfold the gluing construction.

## Scope and API boundaries

- **Universes:** both spaces use `RingedSpace.{u, u}`, and both cover index
  types use `Type u`; their product is again `Type u`. This argument uses the
  actual diagonal-universe API, not an independently mixed-universe or generic
  sheafed-space variant.
- **Arbitrary covers:** there is no finiteness assumption. Cover members and
  cross-intersections may be empty. An empty index type forces `X` to have no
  points by the cover condition; the common cover and its extensionality
  argument still apply, without an inhabited-index assumption.
- **Ringed spaces:** no locally ringed-space, scheme, nonzero-ring or extra
  limit-witness hypothesis is added. The conclusion concerns full morphisms
  in the ringed-space category, not a stronger category of morphisms.
- **Existing interfaces:** `glueMorphisms`, `ι_glueMorphisms`, `hom_ext` and
  `pullback_compatibility_iff_intersection` are the library's open-cover APIs;
  `restrictMap` and `restrictMap_ofRestrict` are its restriction APIs. The
  displayed two-cover equivalence is derived by combining them, rather than
  attributed to a separately named Mathlib theorem.

The open-cover transition construction adapts Andrew Yang's Mathlib work.
See the library's [credits and retained notices](../NOTICE.md) for the
underlying formalization provenance and license information.
