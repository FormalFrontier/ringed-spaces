# Historical API reference (navigation-adjusted)

Native source-only signatures for 33 historical Lean modules (281 recorded
public declarations), with their original nonempty docstrings and explicit
missing-doc accounting. Source links below are hand-adjusted to the identical
files at the official published commit
`958b340be6cf1a0bc86c2c378352664c9f7cca62`; this page is **not** a new
native generation or an inventory of the current library. The original
generated Markdown SHA256 is
`31abe5d797e950a0d6df5bc08167634abf872964723c03c85616f417972d0ade`;
its [manifest](api-manifest.json) and generator describe that **unmodified**
output, not the navigation- and prose-adjusted page here. The generated
`OpenCover.rec` has no native record. See the [mathematical overview](../README.md)
and [current API map](README.md) for additions beyond the historical scope.

Signatures preserve native displayed implicit arguments, but contain no
proof bodies. Native display may suppress type annotations on literals;
consult the linked Lean source for elaborated declarations. No external
JavaScript, fonts, dependency website or build cache is bundled.

## Module `RingedSpaces`

> # Ringed spaces
>
> This aggregate import provides restriction maps, literal-intersection compatibility and
> open-cover gluing and inverse-image factorization for full morphisms of ringed spaces.
> It also exposes same-site extension and restriction of scalars for module
> presheaves and sheaves over commutative-ring presheaves and sheaves, including
> the naturally equivalent genuine right-factor tensor construction, and the
> ordinary inverse image of module presheaves along continuous maps, including
> its linear Hom adjunction to native module pushforward.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces.lean)

## Module `RingedSpaces.InverseImage`

> # Inverse-image ringed spaces
>
> For a ringed space `Y` and a continuous map `g : T ⟶ Y.carrier`, `inverseImage Y g`
> has literal carrier `T` and the native inverse-image sheaf of commutative rings. Its
> canonical map to `Y` is the unit of the inverse-image/pushforward adjunction.
> Every full morphism `f : X ⟶ Y` factors through this object for `g = f.hom.base`:
> the first map has identity base and the adjoint of the entire structure-sheaf map.
>
> The construction is not a categorical fiber-product pullback. It uses diagonal
> universes and does not require nonempty spaces, nonzero rings or local rings.
>
> This standalone construction uses the native inverse-image sheaf and the adjunction
> unit. It factors full ringed-space morphisms without a source-repository dependency.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean)

### `AlgebraicGeometry.RingedSpace.inverseImage`

```lean
noncomputable def AlgebraicGeometry.RingedSpace.inverseImage (Y : RingedSpace) {T : TopCat} (g : T ⟶ ↑Y.toPresheafedSpace) : RingedSpace
```

The ringed space on `T` with the native inverse-image sheaf of rings along `g`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L39) (line 39).

### `AlgebraicGeometry.RingedSpace.inverseImage_carrier`

```lean
theorem AlgebraicGeometry.RingedSpace.inverseImage_carrier (Y : RingedSpace) {T : TopCat} (g : T ⟶ ↑Y.toPresheafedSpace) : ↑(Y.inverseImage g).toPresheafedSpace = T
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L45) (line 45).

### `AlgebraicGeometry.RingedSpace.inverseImage_sheaf`

```lean
theorem AlgebraicGeometry.RingedSpace.inverseImage_sheaf (Y : RingedSpace) {T : TopCat} (g : T ⟶ ↑Y.toPresheafedSpace) : SheafedSpace.sheaf (Y.inverseImage g) = (TopCat.Sheaf.pullback CommRingCat g).obj (SheafedSpace.sheaf Y)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L48) (line 48).

### `AlgebraicGeometry.RingedSpace.ofInverseImage`

```lean
noncomputable def AlgebraicGeometry.RingedSpace.ofInverseImage (Y : RingedSpace) {T : TopCat} (g : T ⟶ ↑Y.toPresheafedSpace) : Y.inverseImage g ⟶ Y
```

The canonical full ringed-space morphism induced by the sheaf adjunction unit.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L52) (line 52).

### `AlgebraicGeometry.RingedSpace.ofInverseImage_base`

```lean
theorem AlgebraicGeometry.RingedSpace.ofInverseImage_base (Y : RingedSpace) {T : TopCat} (g : T ⟶ ↑Y.toPresheafedSpace) : (Y.ofInverseImage g).hom.base = g
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L59) (line 59).

### `AlgebraicGeometry.RingedSpace.ofInverseImage_c`

```lean
theorem AlgebraicGeometry.RingedSpace.ofInverseImage_c (Y : RingedSpace) {T : TopCat} (g : T ⟶ ↑Y.toPresheafedSpace) : (Y.ofInverseImage g).hom.c = ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app (SheafedSpace.sheaf Y)).hom
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L62) (line 62).

### `AlgebraicGeometry.RingedSpace.ofInverseImage_c_app`

```lean
theorem AlgebraicGeometry.RingedSpace.ofInverseImage_c_app (Y : RingedSpace) {T : TopCat} (g : T ⟶ ↑Y.toPresheafedSpace) (U : (TopologicalSpace.Opens ↑↑Y.toPresheafedSpace)ᵒᵖ) : (Y.ofInverseImage g).hom.c.app U = ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app (SheafedSpace.sheaf Y)).hom.app U
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L67) (line 67).

### `AlgebraicGeometry.RingedSpace.inverseImageMap`

```lean
noncomputable def AlgebraicGeometry.RingedSpace.inverseImageMap {X Y : RingedSpace} (f : X ⟶ Y) : SheafedSpace.sheaf (Y.inverseImage f.hom.base) ⟶ SheafedSpace.sheaf X
```

The adjoint of the full structure-sheaf morphism of `f`, as a map of ring sheaves.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L74) (line 74).

### `AlgebraicGeometry.RingedSpace.inverseImageMap_unit`

```lean
theorem AlgebraicGeometry.RingedSpace.inverseImageMap_unit {X Y : RingedSpace} (f : X ⟶ Y) : CategoryTheory.CategoryStruct.comp ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).unit.app (SheafedSpace.sheaf Y)) ((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map (inverseImageMap f)) = CategoryTheory.Sheaf.homEquiv.symm f.hom.c
```

The mate equation as an equality of full ring-sheaf maps.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L80) (line 80).

### `AlgebraicGeometry.RingedSpace.inverseImageMap_unit_hom`

```lean
theorem AlgebraicGeometry.RingedSpace.inverseImageMap_unit_hom {X Y : RingedSpace} (f : X ⟶ Y) : (CategoryTheory.CategoryStruct.comp ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).unit.app (SheafedSpace.sheaf Y)) ((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map (inverseImageMap f))).hom = f.hom.c
```

After forgetting to presheaves, the unit equation recovers the given structure map.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L90) (line 90).

### `AlgebraicGeometry.RingedSpace.inverseImageMap_unit_app`

```lean
theorem AlgebraicGeometry.RingedSpace.inverseImageMap_unit_app {X Y : RingedSpace} (f : X ⟶ Y) (U : (TopologicalSpace.Opens ↑↑Y.toPresheafedSpace)ᵒᵖ) : (CategoryTheory.CategoryStruct.comp ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).unit.app (SheafedSpace.sheaf Y)) ((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map (inverseImageMap f))).hom.app U = f.hom.c.app U
```

On every target open, the sheaf unit followed by the pushed-forward mate is `f`'s
ring map on sections.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L102) (line 102).

### `AlgebraicGeometry.RingedSpace.inverseImageMap_unit_components`

```lean
theorem AlgebraicGeometry.RingedSpace.inverseImageMap_unit_components {X Y : RingedSpace} (f : X ⟶ Y) (U : (TopologicalSpace.Opens ↑↑Y.toPresheafedSpace)ᵒᵖ) : CategoryTheory.CategoryStruct.comp (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).unit.app (SheafedSpace.sheaf Y)).hom.app U) (((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map (inverseImageMap f)).hom.app U) = f.hom.c.app U
```

The native unit and the pushed-forward mate compose as ring homomorphisms on every open.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L111) (line 111).

### `AlgebraicGeometry.RingedSpace.toInverseImage`

```lean
noncomputable def AlgebraicGeometry.RingedSpace.toInverseImage {X Y : RingedSpace} (f : X ⟶ Y) : X ⟶ Y.inverseImage f.hom.base
```

The full map from `X` to the inverse-image ringed space, over the identity of `X`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L119) (line 119).

### `AlgebraicGeometry.RingedSpace.toInverseImage_base`

```lean
theorem AlgebraicGeometry.RingedSpace.toInverseImage_base {X Y : RingedSpace} (f : X ⟶ Y) : (toInverseImage f).hom.base = CategoryTheory.CategoryStruct.id ↑X.toPresheafedSpace
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L126) (line 126).

### `AlgebraicGeometry.RingedSpace.toInverseImage_c`

```lean
theorem AlgebraicGeometry.RingedSpace.toInverseImage_c {X Y : RingedSpace} (f : X ⟶ Y) : (toInverseImage f).hom.c = CategoryTheory.CategoryStruct.comp (inverseImageMap f).hom (CategoryTheory.eqToHom ⋯)
```

The first map's entire presheaf component includes the identity-pushforward transport.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L129) (line 129).

### `AlgebraicGeometry.RingedSpace.toInverseImage_c_app`

```lean
theorem AlgebraicGeometry.RingedSpace.toInverseImage_c_app {X Y : RingedSpace} (f : X ⟶ Y) (U : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ) : (toInverseImage f).hom.c.app U = CategoryTheory.CategoryStruct.comp ((inverseImageMap f).hom.app U) ((CategoryTheory.eqToHom ⋯).app U)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L134) (line 134).

### `AlgebraicGeometry.RingedSpace.toInverseImage_c_app_eq`

```lean
theorem AlgebraicGeometry.RingedSpace.toInverseImage_c_app_eq {X Y : RingedSpace} (f : X ⟶ Y) (U : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ) : (toInverseImage f).hom.c.app U = (inverseImageMap f).hom.app U
```

On sections, the identity-pushforward transport acts as the identity.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L139) (line 139).

### `AlgebraicGeometry.RingedSpace.toInverseImage_ofInverseImage`

```lean
theorem AlgebraicGeometry.RingedSpace.toInverseImage_ofInverseImage {X Y : RingedSpace} (f : X ⟶ Y) : CategoryTheory.CategoryStruct.comp (toInverseImage f) (Y.ofInverseImage f.hom.base) = f
```

The two full morphisms compose to the original full morphism, including its sheaf map.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/InverseImage.lean#L145) (line 145).

## Module `RingedSpaces.Modules.PresheafChangeOfRings`

> # Presheaf extension of scalars
>
> Given a full natural transformation of commutative-ring presheaves, construct the
> sectionwise tensor presheaf and its extension/restriction adjunction. Restriction
> is obtained as a mate of the semilinear restriction on pure tensors, and does
> not require a topology or a sheaf condition.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean)

[Mathematical guide](module-change-of-rings.md)

### `RingedSpaces.Modules.ringPresheaf`

```lean
abbrev RingedSpaces.Modules.ringPresheaf {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ CommRingCat) : CategoryTheory.Functor Cᵒᵖ RingCat
```

The underlying presheaf of possibly noncommutative rings.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L31) (line 31).

### `RingedSpaces.Modules.ringMap`

```lean
def RingedSpaces.Modules.ringMap {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) : ringPresheaf A ⟶ ringPresheaf B
```

Forget commutativity of a whole map of ring presheaves.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L35) (line 35).

### `RingedSpaces.Modules.Presheaves`

```lean
abbrev RingedSpaces.Modules.Presheaves {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ CommRingCat) : Type (max (max (max u u₁) (u + 1)) v₁)
```

Module presheaves over a presheaf of commutative rings.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L39) (line 39).

### `RingedSpaces.Modules.tensorSection`

```lean
noncomputable def RingedSpaces.Modules.tensorSection {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) : ModuleCat ↑((ringPresheaf B).obj U)
```

The actual tensor of sections, with its `B(U)` action.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L43) (line 43).

### `RingedSpaces.Modules.tensorUnitSection`

```lean
noncomputable def RingedSpaces.Modules.tensorUnitSection {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) : PresheafOfModulesOfCommRing.obj M U ⟶ (ModuleCat.restrictScalars (RingCat.Hom.hom ((ringMap A B theta).app U))).obj (tensorSection A B theta M U)
```

The sectionwise unit `m ↦ 1 ⊗ m`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L50) (line 50).

### `RingedSpaces.Modules.tensorSectionHomEquiv`

```lean
noncomputable def RingedSpaces.Modules.tensorSectionHomEquiv {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (N : ModuleCat ↑((ringPresheaf B).obj U)) : (tensorSection A B theta M U ⟶ N) ≃ (PresheafOfModulesOfCommRing.obj M U ⟶ (ModuleCat.restrictScalars (RingCat.Hom.hom ((ringMap A B theta).app U))).obj N)
```

The ordinary tensor Hom equivalence on a single open.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L60) (line 60).

### `RingedSpaces.Modules.tensorSectionHomEquiv_apply`

```lean
theorem RingedSpaces.Modules.tensorSectionHomEquiv_apply {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (N : ModuleCat ↑((ringPresheaf B).obj U)) (t : tensorSection A B theta M U ⟶ N) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom ((tensorSectionHomEquiv A B theta M U N) t)) m = (CategoryTheory.ConcreteCategory.hom t) ((CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M U)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L69) (line 69).

### `RingedSpaces.Modules.tensorSectionHomEquiv_symm_unit`

```lean
theorem RingedSpaces.Modules.tensorSectionHomEquiv_symm_unit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (N : ModuleCat ↑((ringPresheaf B).obj U)) (g : PresheafOfModulesOfCommRing.obj M U ⟶ (ModuleCat.restrictScalars (RingCat.Hom.hom ((ringMap A B theta).app U))).obj N) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom ((tensorSectionHomEquiv A B theta M U N).symm g)) ((CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M U)) m) = (CategoryTheory.ConcreteCategory.hom g) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L77) (line 77).

### `RingedSpaces.Modules.restrictionUnit`

```lean
noncomputable def RingedSpaces.Modules.restrictionUnit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) : PresheafOfModulesOfCommRing.obj M U ⟶ (ModuleCat.restrictScalars (RingCat.Hom.hom ((ringMap A B theta).app U))).obj ((ModuleCat.restrictScalars (RingCat.Hom.hom ((ringPresheaf B).map f))).obj (tensorSection A B theta M V))
```

The restriction mate of `m ↦ 1 ⊗ m|`, linear over `A(U)`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L90) (line 90).

### `RingedSpaces.Modules.tensorRestriction`

```lean
noncomputable def RingedSpaces.Modules.tensorRestriction {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) : tensorSection A B theta M U ⟶ (ModuleCat.restrictScalars (RingCat.Hom.hom ((ringPresheaf B).map f))).obj (tensorSection A B theta M V)
```

The `B(U)`-linear restriction mate, targeting the restriction along `B(U) → B(V)`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L137) (line 137).

### `RingedSpaces.Modules.restrictionUnit_apply`

```lean
theorem RingedSpaces.Modules.restrictionUnit_apply {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (restrictionUnit A B theta M f)) m = (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M V)) ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map M f)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L145) (line 145).

### `RingedSpaces.Modules.tensorRestriction_unit`

```lean
theorem RingedSpaces.Modules.tensorRestriction_unit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (tensorRestriction A B theta M f)) ((CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M U)) m) = (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M V)) ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map M f)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L149) (line 149).

### `RingedSpaces.Modules.tensorRestriction_smul`

```lean
theorem RingedSpaces.Modules.tensorRestriction_smul {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) (b : ↑(B.obj U)) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (tensorRestriction A B theta M f)) (b • (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M U)) m) = (CategoryTheory.ConcreteCategory.hom (B.map f)) b • (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M V)) ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map M f)) m)
```

Restriction sends an arbitrary `b ⊗ m` to `B(f)(b) ⊗ M(f)(m)`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L164) (line 164).

### `RingedSpaces.Modules.tensorPresheaf`

```lean
noncomputable def RingedSpaces.Modules.tensorPresheaf {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) : Presheaves B
```

The genuine pointwise tensor presheaf, including its identity and composition laws.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L175) (line 175).

### `RingedSpaces.Modules.tensorSectionMap`

```lean
noncomputable def RingedSpaces.Modules.tensorSectionMap {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) (U : Cᵒᵖ) : tensorSection A B theta M U ⟶ tensorSection A B theta N U
```

The section map `b ⊗ m ↦ b ⊗ h(m)` induced by an `A`-linear sheaf map.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L205) (line 205).

### `RingedSpaces.Modules.tensorSectionMap_unit`

```lean
theorem RingedSpaces.Modules.tensorSectionMap_unit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (tensorSectionMap A B theta h U)) ((CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M U)) m) = (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta N U)) ((CategoryTheory.ConcreteCategory.hom (h.app U)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L212) (line 212).

### `RingedSpaces.Modules.tensorSectionMap_smul`

```lean
theorem RingedSpaces.Modules.tensorSectionMap_smul {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) (U : Cᵒᵖ) (b : ↑(B.obj U)) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (tensorSectionMap A B theta h U)) (b • (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M U)) m) = b • (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta N U)) ((CategoryTheory.ConcreteCategory.hom (h.app U)) m)
```

Maps of tensor presheaves act on arbitrary pure tensors.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L219) (line 219).

### `RingedSpaces.Modules.tensorPresheafMap`

```lean
noncomputable def RingedSpaces.Modules.tensorPresheafMap {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) : tensorPresheaf A B theta M ⟶ tensorPresheaf A B theta N
```

Tensoring a map is compatible with all presheaf restrictions.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L228) (line 228).

### `RingedSpaces.Modules.tensorPresheafFunctor`

```lean
noncomputable def RingedSpaces.Modules.tensorPresheafFunctor {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) : CategoryTheory.Functor (Presheaves A) (Presheaves B)
```

The covariant tensor presheaf functor.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L248) (line 248).

### `RingedSpaces.Modules.presheafTensorUnit`

```lean
noncomputable def RingedSpaces.Modules.presheafTensorUnit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) : M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj (tensorPresheaf A B theta M)
```

The natural presheaf unit before sheafification.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L277) (line 277).

### `RingedSpaces.Modules.tensorPresheafHomDown`

```lean
noncomputable def RingedSpaces.Modules.tensorPresheafHomDown {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {N : Presheaves B} (t : tensorPresheaf A B theta M ⟶ N) : M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N
```

Restrict a presheaf Hom along the local unit `m ↦ 1 ⊗ m`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L288) (line 288).

### `RingedSpaces.Modules.tensorPresheafHomUp`

```lean
noncomputable def RingedSpaces.Modules.tensorPresheafHomUp {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {N : Presheaves B} (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N) : tensorPresheaf A B theta M ⟶ N
```

Extend an `A`-linear presheaf Hom by `b ⊗ m ↦ b • g(m)`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L304) (line 304).

### `RingedSpaces.Modules.tensorPresheafHomUp_smul`

```lean
theorem RingedSpaces.Modules.tensorPresheafHomUp_smul {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {N : Presheaves B} (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N) (U : Cᵒᵖ) (b : ↑(B.obj U)) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom ((tensorPresheafHomUp A B theta M g).app U)) (b • (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M U)) m) = b • (CategoryTheory.ConcreteCategory.hom (g.app U)) m
```

The upward Hom map evaluates `b ⊗ m` as `b • g(m)` for arbitrary `b`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L326) (line 326).

### `RingedSpaces.Modules.tensorPresheafHomEquiv`

```lean
noncomputable def RingedSpaces.Modules.tensorPresheafHomEquiv {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (N : Presheaves B) : (tensorPresheaf A B theta M ⟶ N) ≃ (M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N)
```

The inverse tensor Hom maps, proven compatible with restrictions.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L343) (line 343).

### `RingedSpaces.Modules.tensorPresheafHomDown_naturality_left`

```lean
theorem RingedSpaces.Modules.tensorPresheafHomDown_naturality_left {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M M' : Presheaves A} (h : M ⟶ M') {N : Presheaves B} (t : tensorPresheaf A B theta M' ⟶ N) : tensorPresheafHomDown A B theta M (CategoryTheory.CategoryStruct.comp ((tensorPresheafFunctor A B theta).map h) t) = CategoryTheory.CategoryStruct.comp h (tensorPresheafHomDown A B theta M' t)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L363) (line 363).

### `RingedSpaces.Modules.tensorPresheafHomDown_naturality_right`

```lean
theorem RingedSpaces.Modules.tensorPresheafHomDown_naturality_right {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {N N' : Presheaves B} (t : tensorPresheaf A B theta M ⟶ N) (k : N ⟶ N') : tensorPresheafHomDown A B theta M (CategoryTheory.CategoryStruct.comp t k) = CategoryTheory.CategoryStruct.comp (tensorPresheafHomDown A B theta M t) ((PresheafOfModules.restrictScalars (ringMap A B theta)).map k)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L385) (line 385).

### `RingedSpaces.Modules.tensorPresheafAdjunction`

```lean
noncomputable def RingedSpaces.Modules.tensorPresheafAdjunction {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) : tensorPresheafFunctor A B theta ⊣ PresheafOfModules.restrictScalars (ringMap A B theta)
```

Sectionwise scalar extension is left adjoint to restriction along the full ring map.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L403) (line 403).

### `RingedSpaces.Modules.tensorPresheafAdjunction_unit`

```lean
theorem RingedSpaces.Modules.tensorPresheafAdjunction_unit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (((tensorPresheafAdjunction A B theta).unit.app M).app U)) m = (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M U)) m
```

The adjunction unit is the actual sectionwise map `m ↦ 1 ⊗ m`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L425) (line 425).

### `RingedSpaces.Modules.tensorPresheafAdjunction_counit`

```lean
theorem RingedSpaces.Modules.tensorPresheafAdjunction_counit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (N : Presheaves B) (U : Cᵒᵖ) (b : ↑(B.obj U)) (n : ↑(PresheafOfModulesOfCommRing.obj N U)) : (CategoryTheory.ConcreteCategory.hom (((tensorPresheafAdjunction A B theta).counit.app N).app U)) (b • (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta ((PresheafOfModules.restrictScalars (ringMap A B theta)).obj N) U)) n) = b • n
```

The adjunction counit sends `b ⊗ n` to `b • n` on every section.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRings.lean#L437) (line 437).

## Module `RingedSpaces.Modules.PresheafChangeOfRingsSymmetry`

> # Right-factor order for presheaf extension of scalars
>
> The section tensor is genuinely `M(U) ⊗[A(U)] B(U)`, with the `A(U)` action
> on `B(U)` induced by the component of the ring-presheaf morphism. Tensor
> symmetry transports the `B(U)` action and intertwines all restrictions.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean)

[Mathematical guide](change-of-rings-symmetry.md)

### `RingedSpaces.Modules.rightFactor`

```lean
noncomputable abbrev RingedSpaces.Modules.rightFactor {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (U : Cᵒᵖ) : ModuleCat ↑((ringPresheaf A).obj U)
```

The actual `A(U)`-module `B(U)` obtained by restriction along `theta_U`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L32) (line 32).

### `RingedSpaces.Modules.rightSection`

```lean
noncomputable def RingedSpaces.Modules.rightSection {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) : ModuleCat ↑(A.obj U)
```

The genuine `M(U) ⊗[A(U), theta_U] B(U)` in its original factor order.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L40) (line 40).

### `RingedSpaces.Modules.rightSectionAddEquiv`

```lean
noncomputable def RingedSpaces.Modules.rightSectionAddEquiv {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) : ↑(rightSection A B theta M U) ≃+ ↑(tensorSection A B theta M U)
```

Tensor symmetry as an equivalence of the underlying additive groups.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L51) (line 51).

### `RingedSpaces.Modules.rightModule`

```lean
noncomputable abbrev RingedSpaces.Modules.rightModule {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) : Module ↑((ringPresheaf B).obj U) ↑(rightSection A B theta M U)
```

Transport the native `B(U)`-module structure onto the right-order tensor.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L62) (line 62).

### `RingedSpaces.Modules.rightSectionCat`

```lean
noncomputable def RingedSpaces.Modules.rightSectionCat {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) : ModuleCat ↑((ringPresheaf B).obj U)
```

The right-order tensor as a bundled `B(U)`-module.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L67) (line 67).

### `RingedSpaces.Modules.rightSectionIso`

```lean
noncomputable def RingedSpaces.Modules.rightSectionIso {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) : rightSectionCat A B theta M U ≅ tensorSection A B theta M U
```

Tensor symmetry, linear for the transported action of `B(U)`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L73) (line 73).

### `RingedSpaces.Modules.rightPure`

```lean
noncomputable def RingedSpaces.Modules.rightPure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : ↑(rightSectionCat A B theta M U)
```

The original-order generator `m ⊗ b` for arbitrary `b`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L79) (line 79).

### `RingedSpaces.Modules.leftPure`

```lean
noncomputable def RingedSpaces.Modules.leftPure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (b : ↑(B.obj U)) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : ↑(tensorSection A B theta M U)
```

The opposite-order generator `b ⊗ m` in the accepted extension.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L90) (line 90).

### `RingedSpaces.Modules.rightSectionIso_pure`

```lean
theorem RingedSpaces.Modules.rightSectionIso_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom (rightSectionIso A B theta M U).hom) (rightPure A B theta M U m b) = leftPure A B theta M U b m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L100) (line 100).

### `RingedSpaces.Modules.rightSectionIso_inv_tmul`

```lean
theorem RingedSpaces.Modules.rightSectionIso_inv_tmul {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom (rightSectionIso A B theta M U).inv) (leftPure A B theta M U b m) = rightPure A B theta M U m b
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L116) (line 116).

### `RingedSpaces.Modules.rightSectionSmul`

```lean
noncomputable def RingedSpaces.Modules.rightSectionSmul {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (c : ↑(B.obj U)) (t : ↑(rightSectionCat A B theta M U)) : ↑(rightSectionCat A B theta M U)
```

Explicit scalar action from `rightModule`, without a global instance.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L133) (line 133).

### `RingedSpaces.Modules.smul_pure`

```lean
theorem RingedSpaces.Modules.smul_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b c : ↑(B.obj U)) : rightSectionSmul A B theta M U c (rightPure A B theta M U m b) = rightPure A B theta M U m (c * b)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L139) (line 139).

### `RingedSpaces.Modules.rightASmul_pure`

```lean
theorem RingedSpaces.Modules.rightASmul_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (a : ↑(A.obj U)) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : SMul.smul a (rightPure A B theta M U m b) = rightPure A B theta M U (SMul.smul a m) b
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L156) (line 156).

### `RingedSpaces.Modules.rightBalance_pure`

```lean
theorem RingedSpaces.Modules.rightBalance_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (a : ↑(A.obj U)) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : rightPure A B theta M U (SMul.smul a m) b = rightPure A B theta M U m ((CommRingCat.Hom.hom (theta.app U)) a * b)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L173) (line 173).

### `RingedSpaces.Modules.theta_smul_pure`

```lean
theorem RingedSpaces.Modules.theta_smul_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (a : ↑(A.obj U)) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : SMul.smul a (rightPure A B theta M U m b) = rightSectionSmul A B theta M U ((CommRingCat.Hom.hom (theta.app U)) a) (rightPure A B theta M U m b)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L188) (line 188).

### `RingedSpaces.Modules.theta_smul`

```lean
theorem RingedSpaces.Modules.theta_smul {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (a : ↑(A.obj U)) (t : ↑(rightSectionCat A B theta M U)) : SMul.smul a t = rightSectionSmul A B theta M U ((CommRingCat.Hom.hom (theta.app U)) a) t
```

The native tensor `A(U)`-action is the restriction of its transported `B(U)`-action
on every tensor, not only on pure tensors.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L195) (line 195).

### `RingedSpaces.Modules.unit_eq_leftPure`

```lean
theorem RingedSpaces.Modules.unit_eq_leftPure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M U)) m = leftPure A B theta M U 1 m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L225) (line 225).

### `RingedSpaces.Modules.leftPure_eq_smul_unit`

```lean
theorem RingedSpaces.Modules.leftPure_eq_smul_unit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : leftPure A B theta M U b m = SMul.smul b ((CategoryTheory.ConcreteCategory.hom (tensorUnitSection A B theta M U)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L230) (line 230).

### `RingedSpaces.Modules.rightRestriction`

```lean
noncomputable def RingedSpaces.Modules.rightRestriction {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) : rightSectionCat A B theta M U ⟶ (ModuleCat.restrictScalars (RingCat.Hom.hom ((ringPresheaf B).map f))).obj (rightSectionCat A B theta M V)
```

The original-order restriction, linear after restricting scalars through `B(f)`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L252) (line 252).

### `RingedSpaces.Modules.rightRestriction_comm`

```lean
theorem RingedSpaces.Modules.rightRestriction_comm {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) : CategoryTheory.CategoryStruct.comp (rightSectionIso A B theta M U).hom (tensorRestriction A B theta M f) = CategoryTheory.CategoryStruct.comp (rightRestriction A B theta M f) ((ModuleCat.restrictScalars (RingCat.Hom.hom ((ringPresheaf B).map f))).map (rightSectionIso A B theta M V).hom)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L262) (line 262).

### `RingedSpaces.Modules.oppositeRestriction_pure`

```lean
theorem RingedSpaces.Modules.oppositeRestriction_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom (tensorRestriction A B theta M f)) (leftPure A B theta M U b m) = leftPure A B theta M V ((CommRingCat.Hom.hom (B.map f)) b) ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map M f)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L270) (line 270).

### `RingedSpaces.Modules.rightRestriction_pure`

```lean
theorem RingedSpaces.Modules.rightRestriction_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom (rightRestriction A B theta M f)) (rightPure A B theta M U m b) = rightPure A B theta M V ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map M f)) m) ((CommRingCat.Hom.hom (B.map f)) b)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L299) (line 299).

### `RingedSpaces.Modules.rightRestriction_semilinear`

```lean
theorem RingedSpaces.Modules.rightRestriction_semilinear {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) (c : ↑(B.obj U)) (t : ↑(rightSectionCat A B theta M U)) : (CategoryTheory.ConcreteCategory.hom (rightRestriction A B theta M f)) (rightSectionSmul A B theta M U c t) = rightSectionSmul A B theta M V ((CommRingCat.Hom.hom (B.map f)) c) ((CategoryTheory.ConcreteCategory.hom (rightRestriction A B theta M f)) t)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L309) (line 309).

### `RingedSpaces.Modules.rightPresheaf`

```lean
noncomputable def RingedSpaces.Modules.rightPresheaf {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) : Presheaves B
```

Actual right-order section tensors and semilinear restrictions form a presheaf.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L328) (line 328).

### `RingedSpaces.Modules.rightPresheafIso`

```lean
noncomputable def RingedSpaces.Modules.rightPresheafIso {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) : rightPresheaf A B theta M ≅ tensorPresheaf A B theta M
```

The right-order presheaf is naturally equivalent to the accepted one.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L371) (line 371).

### `RingedSpaces.Modules.rightPresheafMap`

```lean
noncomputable def RingedSpaces.Modules.rightPresheafMap {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) : rightPresheaf A B theta M ⟶ rightPresheaf A B theta N
```

Sectionwise tensoring of an `A`-module sheaf morphism, in right order.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L377) (line 377).

### `RingedSpaces.Modules.oppositeMap_pure`

```lean
theorem RingedSpaces.Modules.oppositeMap_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom (tensorSectionMap A B theta h U)) (leftPure A B theta M U b m) = leftPure A B theta N U b ((CategoryTheory.ConcreteCategory.hom (h.app U)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L383) (line 383).

### `RingedSpaces.Modules.rightSectionMap`

```lean
noncomputable def RingedSpaces.Modules.rightSectionMap {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) (U : Cᵒᵖ) : rightSectionCat A B theta M U ⟶ rightSectionCat A B theta N U
```

The right-order component of `rightPresheafMap` on one open.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L400) (line 400).

### `RingedSpaces.Modules.rightSectionMap_pure`

```lean
theorem RingedSpaces.Modules.rightSectionMap_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom (rightSectionMap A B theta h U)) (rightPure A B theta M U m b) = rightPure A B theta N U ((CategoryTheory.ConcreteCategory.hom (h.app U)) m) b
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L407) (line 407).

### `RingedSpaces.Modules.rightPresheafMap_pure`

```lean
theorem RingedSpaces.Modules.rightPresheafMap_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom ((rightPresheafMap A B theta h).app U)) (rightPure A B theta M U m b) = rightPure A B theta N U ((CategoryTheory.ConcreteCategory.hom (h.app U)) m) b
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L417) (line 417).

### `RingedSpaces.Modules.rightPresheafMap_restriction`

```lean
theorem RingedSpaces.Modules.rightPresheafMap_restriction {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : Presheaves A} (h : M ⟶ N) {U V : Cᵒᵖ} (f : U ⟶ V) (t : ↑(rightSectionCat A B theta M U)) : (CategoryTheory.ConcreteCategory.hom (rightRestriction A B theta N f)) ((CategoryTheory.ConcreteCategory.hom (rightSectionMap A B theta h U)) t) = (CategoryTheory.ConcreteCategory.hom (rightSectionMap A B theta h V)) ((CategoryTheory.ConcreteCategory.hom (rightRestriction A B theta M f)) t)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L423) (line 423).

### `RingedSpaces.Modules.rightUnitSection`

```lean
noncomputable def RingedSpaces.Modules.rightUnitSection {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) : PresheafOfModulesOfCommRing.obj M U ⟶ (ModuleCat.restrictScalars (RingCat.Hom.hom ((ringMap A B theta).app U))).obj (rightSectionCat A B theta M U)
```

The sectionwise right-order unit, linear over `A(U)`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L429) (line 429).

### `RingedSpaces.Modules.rightUnitSection_pure`

```lean
theorem RingedSpaces.Modules.rightUnitSection_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (rightUnitSection A B theta M U)) m = rightPure A B theta M U m 1
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L438) (line 438).

### `RingedSpaces.Modules.rightPresheafUnit`

```lean
noncomputable def RingedSpaces.Modules.rightPresheafUnit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) : M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj (rightPresheaf A B theta M)
```

The compatible presheaf unit `m ↦ m ⊗ 1`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L445) (line 445).

### `RingedSpaces.Modules.rightPresheafUnit_pure`

```lean
theorem RingedSpaces.Modules.rightPresheafUnit_pure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom ((rightPresheafUnit A B theta M).app U)) m = rightPure A B theta M U m 1
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L453) (line 453).

### `RingedSpaces.Modules.rightPresheafFunctor`

```lean
noncomputable def RingedSpaces.Modules.rightPresheafFunctor {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) : CategoryTheory.Functor (Presheaves A) (Presheaves B)
```

Functoriality in the `A`-module presheaf input.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L469) (line 469).

### `RingedSpaces.Modules.rightPresheafNatIso`

```lean
noncomputable def RingedSpaces.Modules.rightPresheafNatIso {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) : rightPresheafFunctor A B theta ≅ tensorPresheafFunctor A B theta
```

The natural presheaf-level tensor symmetry, including module-map naturality.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafChangeOfRingsSymmetry.lean#L499) (line 499).

## Module `RingedSpaces.Modules.PresheafInverseImage`

> # Inverse image of a module presheaf along a continuous map
>
> The neighborhood-colimit ring acts on the neighborhood-colimit additive presheaf.
> The action and restriction maps are those of the actual pointwise left Kan extensions;
> the underlying additive presheaf is naturally the usual inverse image.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean)

[Mathematical guide](presheaf-inverse-image.md)

### `RingedSpaces.Modules.PresheafInverseImage.index`

```lean
abbrev RingedSpaces.Modules.PresheafInverseImage.index {X Y : TopCat} (f : X ⟶ Y) (U : TopologicalSpace.Opens ↑X) : Type v
```

Open neighborhoods of the image of `U`, ordered in the colimit direction.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L32) (line 32).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseModule`

```lean
noncomputable instance RingedSpaces.Modules.PresheafInverseImage.pointwiseModule {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (U : TopologicalSpace.Opens ↑X) : Module ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj (Opposite.op U)) ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (Opposite.op U))
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L134) (line 134).

### `RingedSpaces.Modules.PresheafInverseImage.pointwise_smul_ι`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.pointwise_smul_ι {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (U : TopologicalSpace.Opens ↑X) (i : index f U) (r : ↑(R.obj (CategoryTheory.CostructuredArrow.left i))) (m : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) (r • m) = (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp R) i)) r • (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L181) (line 181).

### `RingedSpaces.Modules.PresheafInverseImage.ring_map_ι`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.ring_map_ι {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {U V : TopologicalSpace.Opens ↑X} (g : Opposite.op U ⟶ Opposite.op V) (i : index f U) (r : ↑(R.obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).map g)) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp R) i)) r) = (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op V)).comp R) ((CategoryTheory.CostructuredArrow.map g).obj i))) r
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L214) (line 214).

### `RingedSpaces.Modules.PresheafInverseImage.group_map_ι`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.group_map_ι {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {U V : TopologicalSpace.Opens ↑X} (g : Opposite.op U ⟶ Opposite.op V) (i : index f U) (m : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).map g)) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) m) = (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op V)).comp M.presheaf) ((CategoryTheory.CostructuredArrow.map g).obj i))) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L225) (line 225).

### `RingedSpaces.Modules.PresheafInverseImage.pointwise_jointly_surjective`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.pointwise_jointly_surjective {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (U : TopologicalSpace.Opens ↑X) (r : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj (Opposite.op U))) (m : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (Opposite.op U))) : ∃ (i : index f U) (a : ↑(R.obj (CategoryTheory.CostructuredArrow.left i))) (b : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))), (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp R) i)) a = r ∧ (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) b = m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L237) (line 237).

### `RingedSpaces.Modules.PresheafInverseImage.restriction_smul`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.restriction_smul {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {U V : TopologicalSpace.Opens ↑X} (g : Opposite.op U ⟶ Opposite.op V) (r : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj (Opposite.op U))) (m : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).map g)) (r • m) = (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).map g)) r • (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).map g)) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L258) (line 258).

### `RingedSpaces.Modules.PresheafInverseImage.inverseImageModule`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.inverseImageModule {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)
```

The ordinary inverse-image additive presheaf equipped with its neighborhood-colimit action.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L274) (line 274).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseToPullback`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.pointwiseToPullback {X Y : TopCat} (f : X ⟶ Y) (C : Type (v + 1)) [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimits C] (F : TopCat.Presheaf C Y) : (TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension F ≅ (TopCat.Presheaf.pullback C f).obj F
```

Compare a pointwise Kan extension to the chosen presheaf inverse image.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L286) (line 286).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseMap`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.pointwiseMap {X Y : TopCat} (f : X ⟶ Y) {R : TopCat.Presheaf RingCat Y} {M N : PresheafOfModules R} (φ : M ⟶ N) : (TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf ⟶ (TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension N.presheaf
```

Apply an input module morphism on each Kan-colimit generator.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L298) (line 298).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_ι`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_ι {X Y : TopCat} (f : X ⟶ Y) {R : TopCat.Presheaf RingCat Y} {M N : PresheafOfModules R} (φ : M ⟶ N) (U : TopologicalSpace.Opens ↑X) (i : index f U) (m : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom ((pointwiseMap f φ).app (Opposite.op U))) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) m) = (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp N.presheaf) i)) ((CategoryTheory.ConcreteCategory.hom (φ.app (CategoryTheory.CostructuredArrow.left i))) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L316) (line 316).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_smul`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_smul {X Y : TopCat} (f : X ⟶ Y) {R : TopCat.Presheaf RingCat Y} {M N : PresheafOfModules R} (φ : M ⟶ N) (U : TopologicalSpace.Opens ↑X) (r : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj (Opposite.op U))) (m : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom ((pointwiseMap f φ).app (Opposite.op U))) (r • m) = r • (CategoryTheory.ConcreteCategory.hom ((pointwiseMap f φ).app (Opposite.op U))) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L328) (line 328).

### `RingedSpaces.Modules.PresheafInverseImage.inverseImageMap`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.inverseImageMap {X Y : TopCat} (f : X ⟶ Y) {R : TopCat.Presheaf RingCat Y} {M N : PresheafOfModules R} (φ : M ⟶ N) : inverseImageModule f R M ⟶ inverseImageModule f R N
```

The module-linear map induced on ordinary presheaf inverse images.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L343) (line 343).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_id`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_id {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) : pointwiseMap f (CategoryTheory.CategoryStruct.id M) = CategoryTheory.CategoryStruct.id ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L350) (line 350).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_comp`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_comp {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M N P : PresheafOfModules R} (φ : M ⟶ N) (ψ : N ⟶ P) : pointwiseMap f (CategoryTheory.CategoryStruct.comp φ ψ) = CategoryTheory.CategoryStruct.comp (pointwiseMap f φ) (pointwiseMap f ψ)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L363) (line 363).

### `RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) : CategoryTheory.Functor (PresheafOfModules R) (PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R))
```

Ordinary inverse image as a functor on presheaves of modules.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L384) (line 384).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_unit`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.pointwiseMap_unit {X Y : TopCat} (f : X ⟶ Y) {R : TopCat.Presheaf RingCat Y} {M N : PresheafOfModules R} (φ : M ⟶ N) : CategoryTheory.CategoryStruct.comp ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf) ((TopologicalSpace.Opens.map f).op.whiskerLeft (pointwiseMap f φ)) = CategoryTheory.CategoryStruct.comp ((PresheafOfModules.toPresheaf R).map φ) ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit N.presheaf)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L397) (line 397).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseToPullback_fac`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.pointwiseToPullback_fac {X Y : TopCat} (f : X ⟶ Y) (F : TopCat.Presheaf AddCommGrpCat Y) : CategoryTheory.CategoryStruct.comp ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit F) ((TopologicalSpace.Opens.map f).op.whiskerLeft (pointwiseToPullback f AddCommGrpCat F).hom) = (TopologicalSpace.Opens.map f).op.leftKanExtensionUnit F
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L410) (line 410).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseSmul`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.pointwiseSmul {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (U : TopologicalSpace.Opens ↑X) (r : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj (Opposite.op U))) (m : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (Opposite.op U))) : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (Opposite.op U))
```

The pointwise scalar operation, with its module instance explicitly selected.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L420) (line 420).

### `RingedSpaces.Modules.PresheafInverseImage.pointwiseSmul_eq`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.pointwiseSmul_eq {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (U : TopologicalSpace.Opens ↑X) (i : index f U) (r : ↑(R.obj (CategoryTheory.CostructuredArrow.left i))) (m : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))) : pointwiseSmul f R M U ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp R) i)) r) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) m) = (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) (r • m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L429) (line 429).

### `RingedSpaces.Modules.PresheafInverseImage.unit_smul`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.unit_smul {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (V : (TopologicalSpace.Opens ↑Y)ᵒᵖ) (r : ↑(R.obj V)) (m : ↑(M.obj V)) : pointwiseSmul f R M ((TopologicalSpace.Opens.map f).obj (Opposite.unop V)) ((CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R).app V)) r) ((CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V)) m) = (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V)) (r • m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L439) (line 439).

### `RingedSpaces.Modules.PresheafInverseImage.underlyingComparison`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.underlyingComparison {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) : (inverseImageFunctor f R).comp (PresheafOfModules.toPresheaf ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) ≅ (PresheafOfModules.toPresheaf R).comp (TopCat.Presheaf.pullback AddCommGrpCat f)
```

The ordinary additive presheaf inverse image is naturally the underlying functor.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImage.lean#L450) (line 450).

## Module `RingedSpaces.Modules.PresheafInverseImageHom`

> # Hom adjunction for inverse-image module presheaves
>
> For a continuous map of spaces, the ordinary inverse-image module-presheaf
> functor is left adjoint to the corresponding pushforward of modules. The
> forward and backward natural transformations identify the actual action on
> sections and expose the unit, counit and natural Hom equivalence.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean)

[Mathematical guide](presheaf-inverse-image-hom.md)

### `RingedSpaces.Modules.PresheafInverseImage.forward`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.forward {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M : PresheafOfModules R} {N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (g : (inverseImageFunctor f R).obj M ⟶ N) : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N
```

The actual additive Kan-unit map, shown linear over the source ring.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L136) (line 136).

### `RingedSpaces.Modules.PresheafInverseImage.backward`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.backward {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M : PresheafOfModules R} {N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) : (inverseImageFunctor f R).obj M ⟶ N
```

The native Kan descent, shown linear over every pointwise-colimit ring section.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L165) (line 165).

### `RingedSpaces.Modules.PresheafInverseImage.backward_smul`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.backward_smul {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M : PresheafOfModules R} {N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) (U : (TopologicalSpace.Opens ↑X)ᵒᵖ) (r : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj U)) (m : ↑(((inverseImageFunctor f R).obj M).obj U)) : (CategoryTheory.ConcreteCategory.hom ((backward f R h).app U)) (r • m) = r • (CategoryTheory.ConcreteCategory.hom ((backward f R h).app U)) m
```

Kan descent is linear over every coefficient of the actual pointwise Kan ring.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L203) (line 203).

### `RingedSpaces.Modules.PresheafInverseImage.backward_ι`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.backward_ι {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M : PresheafOfModules R} {N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) (U : TopologicalSpace.Opens ↑X) (i : index f U) (m : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom ((backward f R h).app (Opposite.op U))) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) m) = (CategoryTheory.ConcreteCategory.hom (N.map (CategoryTheory.CostructuredArrow.hom i))) ((CategoryTheory.ConcreteCategory.hom (h.app (CategoryTheory.CostructuredArrow.left i))) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L214) (line 214).

### `RingedSpaces.Modules.PresheafInverseImage.forward_apply`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.forward_apply {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M : PresheafOfModules R} {N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (g : (inverseImageFunctor f R).obj M ⟶ N) (V : (TopologicalSpace.Opens ↑Y)ᵒᵖ) (m : ↑(M.obj V)) : (CategoryTheory.ConcreteCategory.hom ((forward f R g).app V)) m = (CategoryTheory.ConcreteCategory.hom (g.app ((TopologicalSpace.Opens.map f).op.obj V))) ((CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L224) (line 224).

### `RingedSpaces.Modules.PresheafInverseImage.backward_forward`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.backward_forward {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M : PresheafOfModules R} {N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (g : (inverseImageFunctor f R).obj M ⟶ N) : backward f R (forward f R g) = g
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L233) (line 233).

### `RingedSpaces.Modules.PresheafInverseImage.forward_backward`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.forward_backward {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M : PresheafOfModules R} {N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) : forward f R (backward f R h) = h
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L256) (line 256).

### `RingedSpaces.Modules.PresheafInverseImage.forward_naturality_left`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.forward_naturality_left {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M' M : PresheafOfModules R} {N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (φ : M' ⟶ M) (g : (inverseImageFunctor f R).obj M ⟶ N) : forward f R (CategoryTheory.CategoryStruct.comp ((inverseImageFunctor f R).map φ) g) = CategoryTheory.CategoryStruct.comp φ (forward f R g)
```

Naturality in the source module, for complete bundled linear maps.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L278) (line 278).

### `RingedSpaces.Modules.PresheafInverseImage.forward_naturality_right`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.forward_naturality_right {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M : PresheafOfModules R} {N N' : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (g : (inverseImageFunctor f R).obj M ⟶ N) (ψ : N ⟶ N') : forward f R (CategoryTheory.CategoryStruct.comp g ψ) = CategoryTheory.CategoryStruct.comp (forward f R g) ((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map ψ)
```

Naturality in the target module, for complete bundled linear maps.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L303) (line 303).

### `RingedSpaces.Modules.PresheafInverseImage.homEquiv`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.homEquiv {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) : ((inverseImageFunctor f R).obj M ⟶ N) ≃ (M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
```

The full presheaf-module Hom equivalence for the actual neighborhood-colimit action.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L323) (line 323).

### `RingedSpaces.Modules.PresheafInverseImage.adjunction`

```lean
noncomputable def RingedSpaces.Modules.PresheafInverseImage.adjunction {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) : inverseImageFunctor f R ⊣ PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)
```

The actual neighborhood-colimit inverse-image functor is left adjoint to native pushforward.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L351) (line 351).

### `RingedSpaces.Modules.PresheafInverseImage.backward_naturality_left`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.backward_naturality_left {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M' M : PresheafOfModules R} {N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (φ : M' ⟶ M) (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) : backward f R (CategoryTheory.CategoryStruct.comp φ h) = CategoryTheory.CategoryStruct.comp ((inverseImageFunctor f R).map φ) (backward f R h)
```

Naturality of descent with respect to the source module.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L371) (line 371).

### `RingedSpaces.Modules.PresheafInverseImage.backward_naturality_right`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.backward_naturality_right {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M : PresheafOfModules R} {N N' : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) (ψ : N ⟶ N') : backward f R (CategoryTheory.CategoryStruct.comp h ((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map ψ)) = CategoryTheory.CategoryStruct.comp (backward f R h) ψ
```

Naturality of descent with respect to the target module.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L381) (line 381).

### `RingedSpaces.Modules.PresheafInverseImage.unit_app_eq`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.unit_app_eq {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) : (adjunction f R).unit.app M = forward f R (CategoryTheory.CategoryStruct.id ((inverseImageFunctor f R).obj M))
```

The actual unit is the additive Kan unit, bundled as a linear map.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L392) (line 392).

### `RingedSpaces.Modules.PresheafInverseImage.unit_apply`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.unit_apply {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (V : (TopologicalSpace.Opens ↑Y)ᵒᵖ) (m : ↑(M.obj V)) : (CategoryTheory.ConcreteCategory.hom (((adjunction f R).unit.app M).app V)) m = (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V)) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L397) (line 397).

### `RingedSpaces.Modules.PresheafInverseImage.counit_app_eq`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.counit_app_eq {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) : (adjunction f R).counit.app N = backward f R (CategoryTheory.CategoryStruct.id ((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N))
```

The actual counit is Kan descent of the pushforward identity.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L404) (line 404).

### `RingedSpaces.Modules.PresheafInverseImage.counit_ι`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.counit_ι {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) (U : TopologicalSpace.Opens ↑X) (i : index f U) (m : ↑(((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom (((adjunction f R).counit.app N).app (Opposite.op U))) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp ((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).presheaf) i)) m) = (CategoryTheory.ConcreteCategory.hom (N.map (CategoryTheory.CostructuredArrow.hom i))) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L411) (line 411).

### `RingedSpaces.Modules.PresheafInverseImage.unit_naturality`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.unit_naturality {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M M' : PresheafOfModules R} (φ : M ⟶ M') : CategoryTheory.CategoryStruct.comp φ ((adjunction f R).unit.app M') = CategoryTheory.CategoryStruct.comp ((adjunction f R).unit.app M) (((inverseImageFunctor f R).comp (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R))).map φ)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L424) (line 424).

### `RingedSpaces.Modules.PresheafInverseImage.counit_naturality`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.counit_naturality {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {N N' : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (ψ : N ⟶ N') : CategoryTheory.CategoryStruct.comp (((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).comp (inverseImageFunctor f R)).map ψ) ((adjunction f R).counit.app N') = CategoryTheory.CategoryStruct.comp ((adjunction f R).counit.app N) ψ
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L432) (line 432).

### `RingedSpaces.Modules.PresheafInverseImage.forward_underlying_additive`

```lean
theorem RingedSpaces.Modules.PresheafInverseImage.forward_underlying_additive {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {M : PresheafOfModules R} {N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (g : (inverseImageFunctor f R).obj M ⟶ N) : CategoryTheory.CategoryStruct.comp ((PresheafOfModules.toPresheaf R).map (forward f R g)) ((PresheafOfModules.pushforwardCompToPresheaf ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom = ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv M.presheaf N.presheaf) (CategoryTheory.CategoryStruct.comp ((underlyingComparison f R).inv.app M) ((PresheafOfModules.toPresheaf ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)).map g))
```

The forward map is the ordinary additive presheaf transpose, after the accepted
pointwise-to-native pullback comparison in the inverse direction.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/PresheafInverseImageHom.lean#L443) (line 443).

## Module `RingedSpaces.Modules.SheafChangeOfRings`

> # Sheaf extension of scalars
>
> For a map of commutative-ring sheaves on one site, sheafify the sectionwise
> tensor presheaf. The resulting adjunction is to restriction along the whole
> map of ring sheaves. Sections of the sheafification are not asserted to be
> sectionwise tensors.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean)

[Mathematical guide](module-change-of-rings.md)

### `RingedSpaces.Modules.ringSheaf`

```lean
abbrev RingedSpaces.Modules.ringSheaf {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (R : CategoryTheory.Sheaf J CommRingCat) : CategoryTheory.Sheaf J RingCat
```

Forget commutativity of a sheaf of rings.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L42) (line 42).

### `RingedSpaces.Modules.ringSheafMap`

```lean
def RingedSpaces.Modules.ringSheafMap {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) (theta : A ⟶ B) : ringSheaf A ⟶ ringSheaf B
```

A morphism of the underlying sheaves of rings.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L46) (line 46).

### `RingedSpaces.Modules.Sheaves`

```lean
abbrev RingedSpaces.Modules.Sheaves {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (R : CategoryTheory.Sheaf J CommRingCat) : Type (max (max (max u u₁) (u + 1)) v₁)
```

Sheaves of modules over a sheaf of commutative rings.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L50) (line 50).

### `RingedSpaces.Modules.moduleSheafification`

```lean
noncomputable def RingedSpaces.Modules.moduleSheafification {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] : CategoryTheory.Functor (Presheaves B.obj) (Sheaves B)
```

Native sheafification of module presheaves over the existing ring sheaf.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L56) (line 56).

### `RingedSpaces.Modules.moduleSheafificationAdjunction`

```lean
noncomputable def RingedSpaces.Modules.moduleSheafificationAdjunction {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] : moduleSheafification B ⊣ (SheafOfModules.forget (ringSheaf B)).comp (PresheafOfModules.restrictScalars (CategoryTheory.CategoryStruct.id (ringSheaf B).obj))
```

The native adjunction governing module sheafification.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L63) (line 63).

### `RingedSpaces.Modules.tensorSheaf`

```lean
noncomputable def RingedSpaces.Modules.tensorSheaf {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) (M : Sheaves A) : Sheaves B
```

The tensor sheaf; arbitrary-open sections need not be pure tensors.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L71) (line 71).

### `RingedSpaces.Modules.tensorSheafFunctor`

```lean
noncomputable def RingedSpaces.Modules.tensorSheafFunctor {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) : CategoryTheory.Functor (Sheaves A) (Sheaves B)
```

The explicit sheaf extension-of-scalars functor.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L75) (line 75).

### `RingedSpaces.Modules.tensorSheafHomEquiv`

```lean
noncomputable def RingedSpaces.Modules.tensorSheafHomEquiv {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) (M : Sheaves A) (N : Sheaves B) : ((tensorSheafFunctor A B theta).obj M ⟶ N) ≃ (M ⟶ (SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N)
```

The natural Hom equivalence for the sheafified tensor presheaf.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L80) (line 80).

### `RingedSpaces.Modules.tensorSheafHomEquiv_val`

```lean
theorem RingedSpaces.Modules.tensorSheafHomEquiv_val {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) (M : Sheaves A) (N : Sheaves B) (t : (tensorSheafFunctor A B theta).obj M ⟶ N) : (SheafOfModules.forget (ringSheaf A)).map ((tensorSheafHomEquiv A B theta M N) t) = tensorPresheafHomDown A.obj B.obj theta.hom M.val (((moduleSheafificationAdjunction B).homEquiv (tensorPresheaf A.obj B.obj theta.hom M.val) N) t)
```

After forgetting the sheaf structure, the Hom equivalence restricts a map to `1 ⊗ m`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L90) (line 90).

### `RingedSpaces.Modules.tensorSheafHomEquiv_apply`

```lean
theorem RingedSpaces.Modules.tensorSheafHomEquiv_apply {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) (M : Sheaves A) (N : Sheaves B) (t : (tensorSheafFunctor A B theta).obj M ⟶ N) (U : Cᵒᵖ) (m : ↑(M.val.obj U)) : (CategoryTheory.ConcreteCategory.hom (((tensorSheafHomEquiv A B theta M N) t).val.app U)) m = (CategoryTheory.ConcreteCategory.hom (t.val.app U)) ((CategoryTheory.ConcreteCategory.hom (((moduleSheafificationAdjunction B).unit.app (tensorPresheaf A.obj B.obj theta.hom M.val)).app U)) ((CategoryTheory.ConcreteCategory.hom (tensorUnitSection A.obj B.obj theta.hom M.val U)) m))
```

The sheaf Hom map evaluates via the actual sheafification unit and `1 ⊗ m`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L99) (line 99).

### `RingedSpaces.Modules.tensorSheafHomEquiv_naturality_left`

```lean
theorem RingedSpaces.Modules.tensorSheafHomEquiv_naturality_left {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) {M M' : Sheaves A} (h : M ⟶ M') (N : Sheaves B) (t : (tensorSheafFunctor A B theta).obj M' ⟶ N) : (tensorSheafHomEquiv A B theta M N) (CategoryTheory.CategoryStruct.comp ((tensorSheafFunctor A B theta).map h) t) = CategoryTheory.CategoryStruct.comp h ((tensorSheafHomEquiv A B theta M' N) t)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L122) (line 122).

### `RingedSpaces.Modules.tensorSheafHomEquiv_naturality_right`

```lean
theorem RingedSpaces.Modules.tensorSheafHomEquiv_naturality_right {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) (M : Sheaves A) {N N' : Sheaves B} (t : (tensorSheafFunctor A B theta).obj M ⟶ N) (k : N ⟶ N') : (tensorSheafHomEquiv A B theta M N') (CategoryTheory.CategoryStruct.comp t k) = CategoryTheory.CategoryStruct.comp ((tensorSheafHomEquiv A B theta M N) t) ((SheafOfModules.restrictScalars (ringSheafMap A B theta)).map k)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L140) (line 140).

### `RingedSpaces.Modules.tensorSheafAdjunction`

```lean
noncomputable def RingedSpaces.Modules.tensorSheafAdjunction {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) : tensorSheafFunctor A B theta ⊣ SheafOfModules.restrictScalars (ringSheafMap A B theta)
```

Extension by sheafified tensor is left adjoint to restriction of scalars.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L157) (line 157).

### `RingedSpaces.Modules.tensorSheafAdjunction_unit`

```lean
theorem RingedSpaces.Modules.tensorSheafAdjunction_unit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) (M : Sheaves A) (U : Cᵒᵖ) (m : ↑(M.val.obj U)) : (CategoryTheory.ConcreteCategory.hom (((tensorSheafAdjunction A B theta).unit.app M).val.app U)) m = (CategoryTheory.ConcreteCategory.hom (((moduleSheafificationAdjunction B).unit.app (tensorPresheaf A.obj B.obj theta.hom M.val)).app U)) ((CategoryTheory.ConcreteCategory.hom (tensorUnitSection A.obj B.obj theta.hom M.val U)) m)
```

The sheaf unit on `m` is the sheafification of `1 ⊗ m`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L175) (line 175).

### `RingedSpaces.Modules.tensorSheafAdjunction_counit`

```lean
theorem RingedSpaces.Modules.tensorSheafAdjunction_counit {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) (N : Sheaves B) (U : Cᵒᵖ) (b : ↑(B.obj.obj U)) (n : ↑(N.val.obj U)) : (CategoryTheory.ConcreteCategory.hom (((tensorSheafAdjunction A B theta).counit.app N).val.app U)) ((CategoryTheory.ConcreteCategory.hom (((moduleSheafificationAdjunction B).unit.app (tensorPresheaf A.obj B.obj theta.hom ((SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N).val)).app U)) (b • (CategoryTheory.ConcreteCategory.hom (tensorUnitSection A.obj B.obj theta.hom ((SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N).val U)) n)) = b • n
```

The sheaf counit extends `b ⊗ n ↦ b • n` through the genuine sheafification unit.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L221) (line 221).

### `RingedSpaces.Modules.opensWeakSheafify`

```lean
theorem RingedSpaces.Modules.opensWeakSheafify (X : TopCat) : CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat
```

The topological open site supplies native weak sheafification.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L250) (line 250).

### `RingedSpaces.Modules.opensWEqualsLocallyBijective`

```lean
theorem RingedSpaces.Modules.opensWEqualsLocallyBijective (X : TopCat) : (Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat
```

The topological open site satisfies native local-bijection detection.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L255) (line 255).

### `RingedSpaces.Modules.opensTensorSheafAdjunction`

```lean
noncomputable def RingedSpaces.Modules.opensTensorSheafAdjunction {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) : tensorSheafFunctor A B theta ⊣ SheafOfModules.restrictScalars (ringSheafMap A B theta)
```

A topological open site discharges every sheaf-level hypothesis at matched universes.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRings.lean#L260) (line 260).

## Module `RingedSpaces.Modules.SheafChangeOfRingsSymmetry`

> # Right-factor scalar extension of module sheaves
>
> Sheafifying the genuine right-factor tensor presheaf is naturally isomorphic
> to the ordinary sheafified scalar extension. This does not identify sections
> of a sheafification on an arbitrary open with raw tensor products.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRingsSymmetry.lean)

[Mathematical guide](change-of-rings-symmetry.md)

### `RingedSpaces.Modules.rightSheafFunctor`

```lean
noncomputable def RingedSpaces.Modules.rightSheafFunctor {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) : CategoryTheory.Functor (Sheaves A) (Sheaves B)
```

Apply right-factor scalar extension before sheafifying.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRingsSymmetry.lean#L33) (line 33).

### `RingedSpaces.Modules.rightSheafNatIso`

```lean
noncomputable def RingedSpaces.Modules.rightSheafNatIso {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) : rightSheafFunctor A B theta ≅ tensorSheafFunctor A B theta
```

Sheafification of the right-factor presheaf agrees with scalar extension.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRingsSymmetry.lean#L38) (line 38).

### `RingedSpaces.Modules.rightSheafificationUnit_naturality`

```lean
theorem RingedSpaces.Modules.rightSheafificationUnit_naturality {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) (M : Sheaves A) : CategoryTheory.CategoryStruct.comp (rightPresheafIso A.obj B.obj theta.hom M.val).hom ((moduleSheafificationAdjunction B).unit.app (tensorPresheaf A.obj B.obj theta.hom M.val)) = CategoryTheory.CategoryStruct.comp ((moduleSheafificationAdjunction B).unit.app (rightPresheaf A.obj B.obj theta.hom M.val)) (((SheafOfModules.forget (ringSheaf B)).comp (PresheafOfModules.restrictScalars (CategoryTheory.CategoryStruct.id (ringSheaf B).obj))).map ((rightSheafNatIso A B theta).hom.app M))
```

Tensor symmetry commutes with the actual module-sheafification unit.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRingsSymmetry.lean#L45) (line 45).

### `RingedSpaces.Modules.opensRightSheafNatIso`

```lean
noncomputable def RingedSpaces.Modules.opensRightSheafNatIso {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) : rightSheafFunctor A B theta ≅ tensorSheafFunctor A B theta
```

The diagonal open site has the existing weak-sheafification witnesses.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Modules/SheafChangeOfRingsSymmetry.lean#L58) (line 58).

## Module `RingedSpaces.OpenCover`

> # Gluing morphisms of ringed spaces along open covers
>
> Compatible morphisms from the canonical restrictions of a ringed space to the members of
> an indexed open cover glue to a unique morphism of ringed spaces. The restrictions and
> equalities here are in the category of ringed spaces, including their structure-sheaf maps.
>
> The construction uses the sheafed-space gluing machinery in mathlib. Its internal comparison
> between the glued multicoequalizer and the original ringed space is proved by checking the
> carrier topology, injectivity, stalk maps, and surjectivity. The proof of the categorical
> transition maps is adapted from the generic portion of mathlib's
> `Mathlib/AlgebraicGeometry/Gluing.lean` (Andrew Yang, Apache 2.0); no scheme hypotheses
> are used here. The comparison proof is adapted from a previously reviewed research proof.
>
> The present universe boundary is diagonal: the source, target and cover index live in
> `RingedSpace.{u, u}` and `Type u`, respectively.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean)

### `AlgebraicGeometry.RingedSpace.OpenCover`

```lean
structure AlgebraicGeometry.RingedSpace.OpenCover (X : RingedSpace) : Type (u + 1)
```

A small indexed open cover of a ringed space. The family may be empty when the source
is empty, and any member of the family may itself be empty.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L42) (line 42).

### `AlgebraicGeometry.RingedSpace.OpenCover.mk`

```lean
constructor AlgebraicGeometry.RingedSpace.OpenCover.mk : {X : AlgebraicGeometry.RingedSpace} → (J : Type u) → (U : J → TopologicalSpace.Opens ↑↑X.toPresheafedSpace) → (∀ (x : ↑↑X.toPresheafedSpace), ∃ (i : J), x ∈ U i) → X.OpenCover
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L42) (line 42).

### `AlgebraicGeometry.RingedSpace.OpenCover.J`

```lean
abbrev AlgebraicGeometry.RingedSpace.OpenCover.J {X : RingedSpace} (self : X.OpenCover) : Type u
```

The type indexing the members of the cover.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L46) (line 46).

### `AlgebraicGeometry.RingedSpace.OpenCover.U`

```lean
abbrev AlgebraicGeometry.RingedSpace.OpenCover.U {X : RingedSpace} (self : X.OpenCover) : self.J → TopologicalSpace.Opens ↑↑X.toPresheafedSpace
```

The indexed open subsets of the underlying topological space.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L48) (line 48).

### `AlgebraicGeometry.RingedSpace.OpenCover.covers`

```lean
theorem AlgebraicGeometry.RingedSpace.OpenCover.covers {X : RingedSpace} (self : X.OpenCover) (x : ↑↑X.toPresheafedSpace) : ∃ (i : self.J), x ∈ self.U i
```

Each point of the source belongs to some member.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L50) (line 50).

### `AlgebraicGeometry.RingedSpace.OpenCover.obj`

```lean
abbrev AlgebraicGeometry.RingedSpace.OpenCover.obj {X : RingedSpace} (C : X.OpenCover) (i : C.J) : RingedSpace
```

The canonical restriction of the ringed space to a cover member.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L56) (line 56).

### `AlgebraicGeometry.RingedSpace.OpenCover.ι`

```lean
abbrev AlgebraicGeometry.RingedSpace.OpenCover.ι {X : RingedSpace} (C : X.OpenCover) (i : C.J) : C.obj i ⟶ X
```

The canonical inclusion of a restricted member into the ringed space, as a full morphism.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L60) (line 60).

### `AlgebraicGeometry.RingedSpace.OpenCover.glueMorphisms`

```lean
noncomputable def AlgebraicGeometry.RingedSpace.OpenCover.glueMorphisms {X : RingedSpace} (C : X.OpenCover) {Y : RingedSpace} (f : (i : C.J) → C.obj i ⟶ Y) (hf : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (C.ι i) (C.ι j)) (f i) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (C.ι i) (C.ι j)) (f j)) : X ⟶ Y
```

Glue pairwise compatible full morphisms from the canonical open restrictions to a target
ringed space. Compatibility is equality of morphisms from each categorical pullback.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L302) (line 302).

### `AlgebraicGeometry.RingedSpace.OpenCover.ι_glueMorphisms`

```lean
theorem AlgebraicGeometry.RingedSpace.OpenCover.ι_glueMorphisms {X : RingedSpace} (C : X.OpenCover) {Y : RingedSpace} (f : (i : C.J) → C.obj i ⟶ Y) (hf : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (C.ι i) (C.ι j)) (f i) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (C.ι i) (C.ι j)) (f j)) (i : C.J) : CategoryTheory.CategoryStruct.comp (C.ι i) (C.glueMorphisms f hf) = f i
```

The glued full morphism restricts literally to each prescribed cover-member morphism.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L518) (line 518).

### `AlgebraicGeometry.RingedSpace.OpenCover.ι_glueMorphisms_assoc`

```lean
theorem AlgebraicGeometry.RingedSpace.OpenCover.ι_glueMorphisms_assoc {X : RingedSpace} (C : X.OpenCover) {Y : RingedSpace} (f : (i : C.J) → C.obj i ⟶ Y) (hf : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (C.ι i) (C.ι j)) (f i) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (C.ι i) (C.ι j)) (f j)) (i : C.J) {Z : RingedSpace} (h : Y ⟶ Z) : CategoryTheory.CategoryStruct.comp (C.ι i) (CategoryTheory.CategoryStruct.comp (C.glueMorphisms f hf) h) = CategoryTheory.CategoryStruct.comp (f i) h
```

The glued full morphism restricts literally to each prescribed cover-member morphism.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L519) (line 519).

### `AlgebraicGeometry.RingedSpace.OpenCover.hom_ext`

```lean
theorem AlgebraicGeometry.RingedSpace.OpenCover.hom_ext {X : RingedSpace} (C : X.OpenCover) {Y : RingedSpace} (f g : X ⟶ Y) (h : ∀ (i : C.J), CategoryTheory.CategoryStruct.comp (C.ι i) f = CategoryTheory.CategoryStruct.comp (C.ι i) g) : f = g
```

Full morphisms from a ringed space are equal if their restrictions to every cover member
are equal, including the induced maps of structure sheaves.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L531) (line 531).

### `AlgebraicGeometry.RingedSpace.OpenCover.existsUnique_gluing`

```lean
theorem AlgebraicGeometry.RingedSpace.OpenCover.existsUnique_gluing {X : RingedSpace} (C : X.OpenCover) {Y : RingedSpace} (f : (i : C.J) → C.obj i ⟶ Y) (hf : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (C.ι i) (C.ι j)) (f i) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (C.ι i) (C.ι j)) (f j)) : ∃! g : X ⟶ Y, ∀ (i : C.J), CategoryTheory.CategoryStruct.comp (C.ι i) g = f i
```

A compatible family of full morphisms on an arbitrary indexed open cover has exactly
one extension to the original ringed space.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L545) (line 545).

### `AlgebraicGeometry.RingedSpace.OpenCover.pullback_compatibility_iff_intersection`

```lean
theorem AlgebraicGeometry.RingedSpace.OpenCover.pullback_compatibility_iff_intersection {X : RingedSpace} (C : X.OpenCover) {Y : RingedSpace} (f : (i : C.J) → C.obj i ⟶ Y) : (∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (C.ι i) (C.ι j)) (f i) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (C.ι i) (C.ι j)) (f j)) ↔ ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (restrictMap (C.U i ⊓ C.U j) (C.U i) ⋯) (f i) = CategoryTheory.CategoryStruct.comp (restrictMap (C.U i ⊓ C.U j) (C.U j) ⋯) (f j)
```

Full-morphism compatibility on the literal pairwise open restrictions is equivalent
to compatibility on categorical pullbacks. No choice of pullback model is required
by a caller using the literal-intersection condition.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L559) (line 559).

### `AlgebraicGeometry.RingedSpace.OpenCover.existsUnique_gluing_of_intersection`

```lean
theorem AlgebraicGeometry.RingedSpace.OpenCover.existsUnique_gluing_of_intersection {X : RingedSpace} (C : X.OpenCover) {Y : RingedSpace} (f : (i : C.J) → C.obj i ⟶ Y) (hf : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (restrictMap (C.U i ⊓ C.U j) (C.U i) ⋯) (f i) = CategoryTheory.CategoryStruct.comp (restrictMap (C.U i ⊓ C.U j) (C.U j) ⋯) (f j)) : ∃! g : X ⟶ Y, ∀ (i : C.J), CategoryTheory.CategoryStruct.comp (C.ι i) g = f i
```

A family of full morphisms agreeing on literal pairwise intersections extends
uniquely to the entire ringed space. In particular, this covers empty intersections,
empty cover members, infinite covers and the empty cover of an empty space.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/OpenCover.lean#L581) (line 581).

## Module `RingedSpaces.Restriction`

> # Restriction maps and intersections of open ringed subspaces
>
> The canonical restrictions of a ringed space to two opens intersect in a categorical
> pullback. All maps and equalities are full ringed-space morphisms, including the
> maps of structure sheaves. The construction uses the open-immersion lifting property
> for presheafed spaces and introduces no local-ring assumptions.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Restriction.lean)

### `AlgebraicGeometry.RingedSpace.restrictMap`

```lean
noncomputable def AlgebraicGeometry.RingedSpace.restrictMap {X : RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) (h : U ≤ V) : SheafedSpace.restrict X ⋯ ⟶ SheafedSpace.restrict X ⋯
```

The canonical full morphism from a smaller open restriction to a larger one.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Restriction.lean#L49) (line 49).

### `AlgebraicGeometry.RingedSpace.restrictMap_ofRestrict`

```lean
theorem AlgebraicGeometry.RingedSpace.restrictMap_ofRestrict {X : RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) (h : U ≤ V) : CategoryTheory.CategoryStruct.comp (restrictMap U V h) (SheafedSpace.ofRestrict X ⋯) = SheafedSpace.ofRestrict X ⋯
```

The restriction map factors the original full open inclusion.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Restriction.lean#L62) (line 62).

### `AlgebraicGeometry.RingedSpace.restrictMap_ofRestrict_assoc`

```lean
theorem AlgebraicGeometry.RingedSpace.restrictMap_ofRestrict_assoc {X : RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) (h : U ≤ V) {Z : SheafedSpace CommRingCat} (h✝ : X ⟶ Z) : CategoryTheory.CategoryStruct.comp (restrictMap U V h) (CategoryTheory.CategoryStruct.comp (SheafedSpace.ofRestrict X ⋯) h✝) = CategoryTheory.CategoryStruct.comp (SheafedSpace.ofRestrict X ⋯) h✝
```

The restriction map factors the original full open inclusion.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Restriction.lean#L63) (line 63).

### `AlgebraicGeometry.RingedSpace.restrictMap_base`

```lean
theorem AlgebraicGeometry.RingedSpace.restrictMap_base {X : RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) (h : U ≤ V) (t : ↥U) : (CategoryTheory.ConcreteCategory.hom (restrictMap U V h).hom.base) t = ⟨↑t, ⋯⟩
```

On points, the restriction map is the canonical inclusion of subtypes.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Restriction.lean#L69) (line 69).

### `AlgebraicGeometry.RingedSpace.restrictMap_comp`

```lean
theorem AlgebraicGeometry.RingedSpace.restrictMap_comp {X : RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) {W : TopologicalSpace.Opens ↑↑X.toPresheafedSpace} (hUV : U ≤ V) (hVW : V ≤ W) : CategoryTheory.CategoryStruct.comp (restrictMap U V hUV) (restrictMap V W hVW) = restrictMap U W ⋯
```

Two successive restrictions compose to the direct restriction.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Restriction.lean#L78) (line 78).

### `AlgebraicGeometry.RingedSpace.restrictMap_comp_assoc`

```lean
theorem AlgebraicGeometry.RingedSpace.restrictMap_comp_assoc {X : RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) {W : TopologicalSpace.Opens ↑↑X.toPresheafedSpace} (hUV : U ≤ V) (hVW : V ≤ W) {Z : SheafedSpace CommRingCat} (h : SheafedSpace.restrict X ⋯ ⟶ Z) : CategoryTheory.CategoryStruct.comp (restrictMap U V hUV) (CategoryTheory.CategoryStruct.comp (restrictMap V W hVW) h) = CategoryTheory.CategoryStruct.comp (restrictMap U W ⋯) h
```

Two successive restrictions compose to the direct restriction.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Restriction.lean#L79) (line 79).

### `AlgebraicGeometry.RingedSpace.restrictMap_id`

```lean
theorem AlgebraicGeometry.RingedSpace.restrictMap_id {X : RingedSpace} (U : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) : restrictMap U U ⋯ = CategoryTheory.CategoryStruct.id (SheafedSpace.restrict X ⋯)
```

Restricting to the same open is the identity full morphism.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Restriction.lean#L86) (line 86).

### `AlgebraicGeometry.RingedSpace.isPullback_restrictInf`

```lean
theorem AlgebraicGeometry.RingedSpace.isPullback_restrictInf {X : RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) : CategoryTheory.IsPullback (restrictMap (U ⊓ V) U ⋯) (restrictMap (U ⊓ V) V ⋯) (SheafedSpace.ofRestrict X ⋯) (SheafedSpace.ofRestrict X ⋯)
```

The literal intersection restriction is the full categorical pullback of the two
canonical inclusions. This also holds for empty or non-covering opens.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpaces/Restriction.lean#L93) (line 93).

## Module `RingedSpacesExamples`

> # Aggregate-import examples for ringed spaces and module presheaves
>
> These examples check gluing along arbitrary indexed open covers and literal
> intersections, full inverse-image factorization, and inverse-image module
> presheaf constructions through the public aggregate import.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/RingedSpacesExamples.lean)

## Module `Test.Axioms`

> # Public and downstream-client axiom audit
>
> Each command reports the transitive axioms of a proof-bearing public declaration or client.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Axioms.lean)

## Module `Test.ChangeOfRingsSymmetry`

> # Direct-import consumers of right-factor change of rings
>
> The coefficient map and site are arbitrary in the main clients. The nonidentity
> arrow, zero ring, empty site and topological boundary clients exercise the same API.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean)

### `Test.ChangeOfRingsSymmetry.arbitraryCoefficients`

```lean
theorem Test.ChangeOfRingsSymmetry.arbitraryCoefficients {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b c : ↑(B.obj U)) : RingedSpaces.Modules.rightSectionSmul A B theta M U c (RingedSpaces.Modules.rightPure A B theta M U m b) = RingedSpaces.Modules.rightPure A B theta M U m (c * b)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L31) (line 31).

### `Test.ChangeOfRingsSymmetry.balanceForFullMap`

```lean
theorem Test.ChangeOfRingsSymmetry.balanceForFullMap {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) (a : ↑(A.obj U)) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : RingedSpaces.Modules.rightPure A B theta M U (SMul.smul a m) b = RingedSpaces.Modules.rightPure A B theta M U m ((CommRingCat.Hom.hom (theta.app U)) a * b)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L36) (line 36).

### `Test.ChangeOfRingsSymmetry.arbitraryTensorCompatibility`

```lean
theorem Test.ChangeOfRingsSymmetry.arbitraryTensorCompatibility {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) (a : ↑(A.obj U)) (t : ↑(RingedSpaces.Modules.rightSectionCat A B theta M U)) : SMul.smul a t = RingedSpaces.Modules.rightSectionSmul A B theta M U ((CommRingCat.Hom.hom (theta.app U)) a) t
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L41) (line 41).

### `Test.ChangeOfRingsSymmetry.comparisonBothDirections`

```lean
theorem Test.ChangeOfRingsSymmetry.comparisonBothDirections {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.rightSectionIso A B theta M U).hom) (RingedSpaces.Modules.rightPure A B theta M U m b) = RingedSpaces.Modules.leftPure A B theta M U b m ∧ (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.rightSectionIso A B theta M U).inv) (RingedSpaces.Modules.leftPure A B theta M U b m) = RingedSpaces.Modules.rightPure A B theta M U m b
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L47) (line 47).

### `Test.ChangeOfRingsSymmetry.actualArrowRestriction`

```lean
theorem Test.ChangeOfRingsSymmetry.actualArrowRestriction {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) {V : Cᵒᵖ} (f : U ⟶ V) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b c : ↑(B.obj U)) (t : ↑(RingedSpaces.Modules.rightSectionCat A B theta M U)) : (CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map (RingedSpaces.Modules.rightPresheaf A B theta M) f)) (RingedSpaces.Modules.rightPure A B theta M U m b) = RingedSpaces.Modules.rightPure A B theta M V ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map M f)) m) ((CategoryTheory.ConcreteCategory.hom (B.map f)) b) ∧ (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.rightRestriction A B theta M f)) (RingedSpaces.Modules.rightSectionSmul A B theta M U c t) = RingedSpaces.Modules.rightSectionSmul A B theta M V ((CategoryTheory.ConcreteCategory.hom (B.map f)) c) ((CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.rightRestriction A B theta M f)) t)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L55) (line 55).

### `Test.ChangeOfRingsSymmetry.arbitraryMorphismNaturality`

```lean
theorem Test.ChangeOfRingsSymmetry.arbitraryMorphismNaturality {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) {N : RingedSpaces.Modules.Presheaves A} (h : M ⟶ N) {V : Cᵒᵖ} (f : U ⟶ V) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) (t : ↑(RingedSpaces.Modules.rightSectionCat A B theta M U)) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.rightPresheafFunctor A B theta).map h).app U)) (RingedSpaces.Modules.rightPure A B theta M U m b) = RingedSpaces.Modules.rightPure A B theta N U ((CategoryTheory.ConcreteCategory.hom (h.app U)) m) b ∧ (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.rightRestriction A B theta N f)) ((CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.rightSectionMap A B theta h U)) t) = (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.rightSectionMap A B theta h V)) ((CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.rightRestriction A B theta M f)) t)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L65) (line 65).

### `Test.ChangeOfRingsSymmetry.rightFunctorLaws`

```lean
theorem Test.ChangeOfRingsSymmetry.rightFunctorLaws {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) {N P : RingedSpaces.Modules.Presheaves A} (h : M ⟶ N) (k : N ⟶ P) {V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (t : ↑(RingedSpaces.Modules.rightSectionCat A B theta M U)) : (CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map (RingedSpaces.Modules.rightPresheaf A B theta M) (CategoryTheory.CategoryStruct.comp f g))) t = (CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map (RingedSpaces.Modules.rightPresheaf A B theta M) g)) ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map (RingedSpaces.Modules.rightPresheaf A B theta M) f)) t) ∧ (RingedSpaces.Modules.rightPresheafFunctor A B theta).map (CategoryTheory.CategoryStruct.id M) = CategoryTheory.CategoryStruct.id ((RingedSpaces.Modules.rightPresheafFunctor A B theta).obj M) ∧ (RingedSpaces.Modules.rightPresheafFunctor A B theta).map (CategoryTheory.CategoryStruct.comp h k) = CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.rightPresheafFunctor A B theta).map h) ((RingedSpaces.Modules.rightPresheafFunctor A B theta).map k)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L76) (line 76).

### `Test.ChangeOfRingsSymmetry.rightIdentityOnPure`

```lean
theorem Test.ChangeOfRingsSymmetry.rightIdentityOnPure {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map (RingedSpaces.Modules.rightPresheaf A B theta M) (CategoryTheory.CategoryStruct.id U))) (RingedSpaces.Modules.rightPure A B theta M U m b) = RingedSpaces.Modules.rightPure A B theta M U m b
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L90) (line 90).

### `Test.ChangeOfRingsSymmetry.unitAndComparison`

```lean
theorem Test.ChangeOfRingsSymmetry.unitAndComparison {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.rightPresheafUnit A B theta M).app U)) m = RingedSpaces.Modules.rightPure A B theta M U m 1 ∧ (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.rightPresheafIso A B theta M).hom.app U)) ((CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.rightPresheafUnit A B theta M).app U)) m) = (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.presheafTensorUnit A B theta M).app U)) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L98) (line 98).

### `Test.ChangeOfRingsSymmetry.homFormulaViaComparison`

```lean
theorem Test.ChangeOfRingsSymmetry.homFormulaViaComparison {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) {N : RingedSpaces.Modules.Presheaves B} (g : M ⟶ (PresheafOfModules.restrictScalars (RingedSpaces.Modules.ringMap A B theta)).obj N) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom ((CategoryTheory.CategoryStruct.comp (RingedSpaces.Modules.rightPresheafIso A B theta M).hom (RingedSpaces.Modules.tensorPresheafHomUp A B theta M g)).app U)) (RingedSpaces.Modules.rightPure A B theta M U m b) = b • (CategoryTheory.ConcreteCategory.hom (g.app U)) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L112) (line 112).

### `Test.ChangeOfRingsSymmetry.emptySiteComparison`

```lean
noncomputable def Test.ChangeOfRingsSymmetry.emptySiteComparison (A : CategoryTheory.Functor (CategoryTheory.Discrete PEmpty.{u + 1})ᵒᵖ CommRingCat) : RingedSpaces.Modules.rightPresheafFunctor A A (CategoryTheory.CategoryStruct.id A) ≅ RingedSpaces.Modules.tensorPresheafFunctor A A (CategoryTheory.CategoryStruct.id A)
```

The tensor comparison exists on a site with no objects.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L143) (line 143).

### `Test.ChangeOfRingsSymmetry.zeroRingPresheaf`

```lean
noncomputable def Test.ChangeOfRingsSymmetry.zeroRingPresheaf : CategoryTheory.Functor (Fin 2)ᵒᵖ CommRingCat
```

A constant zero ring, without a nontriviality assumption.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L149) (line 149).

### `Test.ChangeOfRingsSymmetry.zeroRingArrowComparison`

```lean
noncomputable def Test.ChangeOfRingsSymmetry.zeroRingArrowComparison : RingedSpaces.Modules.rightPresheafFunctor zeroRingPresheaf zeroRingPresheaf (CategoryTheory.CategoryStruct.id zeroRingPresheaf) ≅ RingedSpaces.Modules.tensorPresheafFunctor zeroRingPresheaf zeroRingPresheaf (CategoryTheory.CategoryStruct.id zeroRingPresheaf)
```

Tensor comparison also exists for zero coefficient rings.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L153) (line 153).

### `Test.ChangeOfRingsSymmetry.sheafificationComparisonSquare`

```lean
theorem Test.ChangeOfRingsSymmetry.sheafificationComparisonSquare {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat)] (A B : CategoryTheory.Sheaf J CommRingCat) [CategoryTheory.HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] (theta : A ⟶ B) (M : RingedSpaces.Modules.Sheaves A) : CategoryTheory.CategoryStruct.comp (RingedSpaces.Modules.rightPresheafIso A.obj B.obj theta.hom M.val).hom ((RingedSpaces.Modules.moduleSheafificationAdjunction B).unit.app (RingedSpaces.Modules.tensorPresheaf A.obj B.obj theta.hom M.val)) = CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.moduleSheafificationAdjunction B).unit.app (RingedSpaces.Modules.rightPresheaf A.obj B.obj theta.hom M.val)) (((SheafOfModules.forget (RingedSpaces.Modules.ringSheaf B)).comp (PresheafOfModules.restrictScalars (CategoryTheory.CategoryStruct.id (RingedSpaces.Modules.ringSheaf B).obj))).map ((RingedSpaces.Modules.rightSheafNatIso A B theta).hom.app M))
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetry.lean#L170) (line 170).

## Module `Test.ChangeOfRingsSymmetryAxioms`

> # Pinned transitive axiom census for right-factor scalar extension
>
> This driver prints every declaration (including generated and private ones) from
> the five new imported Lean modules by imported module index, then checks its
> own declarations and explicitly prints the public API, critical native endpoints
> and named consumer axioms.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryAxioms.lean)

## Module `Test.ChangeOfRingsSymmetryFixture`

> # A changing coefficient-ring restriction
>
> The arrow from `1` to `0` takes integer coefficients to rational coefficients.
> The natural map from the constant integers to this diagram is the identity at
> `1`, and integer inclusion at `0`.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryFixture.lean)

### `Test.ChangeOfRingsSymmetryFixture.changingRing`

```lean
noncomputable def Test.ChangeOfRingsSymmetryFixture.changingRing : CategoryTheory.Functor (Fin 2)ᵒᵖ CommRingCat
```

Integer coefficients at object `1`, rational coefficients at object `0`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryFixture.lean#L29) (line 29).

### `Test.ChangeOfRingsSymmetryFixture.constantIntegers`

```lean
noncomputable def Test.ChangeOfRingsSymmetryFixture.constantIntegers : CategoryTheory.Functor (Fin 2)ᵒᵖ CommRingCat
```

The constant integer source ring presheaf.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryFixture.lean#L87) (line 87).

### `Test.ChangeOfRingsSymmetryFixture.integerInclusion`

```lean
noncomputable def Test.ChangeOfRingsSymmetryFixture.integerInclusion : constantIntegers ⟶ changingRing
```

Identity at object `1` and integer inclusion into rationals at object `0`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryFixture.lean#L91) (line 91).

### `Test.ChangeOfRingsSymmetryFixture.nonidentityComponentOnTwo`

```lean
theorem Test.ChangeOfRingsSymmetryFixture.nonidentityComponentOnTwo : (CategoryTheory.ConcreteCategory.hom (integerInclusion.app (Opposite.op 0))) 2 = 2
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryFixture.lean#L127) (line 127).

### `Test.ChangeOfRingsSymmetryFixture.integerInclusionNotSurjective`

```lean
theorem Test.ChangeOfRingsSymmetryFixture.integerInclusionNotSurjective : ¬Function.Surjective ⇑(CommRingCat.Hom.hom (integerInclusion.app (Opposite.op 0)))
```

The coefficient component at object `0` genuinely changes rings: it omits `1/2`.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryFixture.lean#L134) (line 134).

### `Test.ChangeOfRingsSymmetryFixture.nontrivialTwoCoefficientRestriction`

```lean
theorem Test.ChangeOfRingsSymmetryFixture.nontrivialTwoCoefficientRestriction (M : RingedSpaces.Modules.Presheaves constantIntegers) (m : ↑(PresheafOfModulesOfCommRing.obj M (Opposite.op 1))) : (CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map (RingedSpaces.Modules.rightPresheaf constantIntegers changingRing integerInclusion M) (CategoryTheory.homOfLE nontrivialTwoCoefficientRestriction._proof_1).op)) (RingedSpaces.Modules.rightSectionSmul constantIntegers changingRing integerInclusion M (Opposite.op 1) 3 (RingedSpaces.Modules.rightPure constantIntegers changingRing integerInclusion M (Opposite.op 1) m 2)) = RingedSpaces.Modules.rightSectionSmul constantIntegers changingRing integerInclusion M (Opposite.op 0) 3 (RingedSpaces.Modules.rightPure constantIntegers changingRing integerInclusion M (Opposite.op 0) ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map M (CategoryTheory.homOfLE nontrivialTwoCoefficientRestriction._proof_1).op)) m) 2)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryFixture.lean#L148) (line 148).

## Module `Test.ChangeOfRingsSymmetryRoot`

> # Aggregate-import clients of right-factor scalar extension

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryRoot.lean)

### `Test.ChangeOfRingsSymmetryRoot.rootComparisonOnArbitraryCoefficient`

```lean
theorem Test.ChangeOfRingsSymmetryRoot.rootComparisonOnArbitraryCoefficient {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) (b : ↑(B.obj U)) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.rightPresheafNatIso A B theta).hom.app M).app U)) (RingedSpaces.Modules.rightPure A B theta M U m b) = RingedSpaces.Modules.leftPure A B theta M U b m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryRoot.lean#L28) (line 28).

### `Test.ChangeOfRingsSymmetryRoot.rootNonidentityDiagram`

```lean
theorem Test.ChangeOfRingsSymmetryRoot.rootNonidentityDiagram (M : RingedSpaces.Modules.Presheaves ChangeOfRingsSymmetryFixture.constantIntegers) (m : ↑(PresheafOfModulesOfCommRing.obj M (Opposite.op 1))) : (CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map (RingedSpaces.Modules.rightPresheaf ChangeOfRingsSymmetryFixture.constantIntegers ChangeOfRingsSymmetryFixture.changingRing ChangeOfRingsSymmetryFixture.integerInclusion M) (CategoryTheory.homOfLE rootNonidentityDiagram._proof_1).op)) (RingedSpaces.Modules.rightSectionSmul ChangeOfRingsSymmetryFixture.constantIntegers ChangeOfRingsSymmetryFixture.changingRing ChangeOfRingsSymmetryFixture.integerInclusion M (Opposite.op 1) 3 (RingedSpaces.Modules.rightPure ChangeOfRingsSymmetryFixture.constantIntegers ChangeOfRingsSymmetryFixture.changingRing ChangeOfRingsSymmetryFixture.integerInclusion M (Opposite.op 1) m 2)) = RingedSpaces.Modules.rightSectionSmul ChangeOfRingsSymmetryFixture.constantIntegers ChangeOfRingsSymmetryFixture.changingRing ChangeOfRingsSymmetryFixture.integerInclusion M (Opposite.op 0) 3 (RingedSpaces.Modules.rightPure ChangeOfRingsSymmetryFixture.constantIntegers ChangeOfRingsSymmetryFixture.changingRing ChangeOfRingsSymmetryFixture.integerInclusion M (Opposite.op 0) ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map M (CategoryTheory.homOfLE rootNonidentityDiagram._proof_1).op)) m) 2)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ChangeOfRingsSymmetryRoot.lean#L34) (line 34).

## Module `Test.InverseImage`

> # Direct-import clients for inverse-image ringed spaces
>
> Only public declarations are used for the arbitrary continuous and full-map clients.
> The fixtures also exercise identity, empty carrier and the zero ring, including a
> nonidentity full map with a constant underlying continuous map.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean)

### `Test.InverseImage.arbitraryContinuous`

```lean
theorem Test.InverseImage.arbitraryContinuous (Y : AlgebraicGeometry.RingedSpace) {T : TopCat} (g : T ⟶ ↑Y.toPresheafedSpace) : ↑(Y.inverseImage g).toPresheafedSpace = T ∧ AlgebraicGeometry.SheafedSpace.sheaf (Y.inverseImage g) = (TopCat.Sheaf.pullback CommRingCat g).obj (AlgebraicGeometry.SheafedSpace.sheaf Y) ∧ (Y.ofInverseImage g).hom.base = g ∧ (Y.ofInverseImage g).hom.c = ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app (AlgebraicGeometry.SheafedSpace.sheaf Y)).hom
```

A continuous map alone determines the literal carrier, ring sheaf and entire unit map.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean#L27) (line 27).

### `Test.InverseImage.unitOnOpen`

```lean
theorem Test.InverseImage.unitOnOpen (Y : AlgebraicGeometry.RingedSpace) {T : TopCat} (g : T ⟶ ↑Y.toPresheafedSpace) (U : (TopologicalSpace.Opens ↑↑Y.toPresheafedSpace)ᵒᵖ) : (Y.ofInverseImage g).hom.c.app U = ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g).unit.app (AlgebraicGeometry.SheafedSpace.sheaf Y)).hom.app U
```

The canonical map's ring homomorphism on each open is the native adjunction unit.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean#L39) (line 39).

### `Test.InverseImage.arbitraryFull`

```lean
theorem Test.InverseImage.arbitraryFull {X Y : AlgebraicGeometry.RingedSpace} (f : X ⟶ Y) : (AlgebraicGeometry.RingedSpace.toInverseImage f).hom.base = CategoryTheory.CategoryStruct.id ↑X.toPresheafedSpace ∧ (Y.ofInverseImage f.hom.base).hom.base = f.hom.base ∧ CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.toInverseImage f) (Y.ofInverseImage f.hom.base) = f ∧ (CategoryTheory.CategoryStruct.comp ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).unit.app (AlgebraicGeometry.SheafedSpace.sheaf Y)) ((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map (AlgebraicGeometry.RingedSpace.inverseImageMap f))).hom = f.hom.c
```

An arbitrary full morphism has the mate, both base maps and full factorization.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean#L46) (line 46).

### `Test.InverseImage.componentOnOpen`

```lean
theorem Test.InverseImage.componentOnOpen {X Y : AlgebraicGeometry.RingedSpace} (f : X ⟶ Y) (U : (TopologicalSpace.Opens ↑↑Y.toPresheafedSpace)ᵒᵖ) (V : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ) : CategoryTheory.CategoryStruct.comp ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).unit.app (AlgebraicGeometry.SheafedSpace.sheaf Y)) ((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map (AlgebraicGeometry.RingedSpace.inverseImageMap f)) = CategoryTheory.Sheaf.homEquiv.symm f.hom.c ∧ (CategoryTheory.CategoryStruct.comp ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).unit.app (AlgebraicGeometry.SheafedSpace.sheaf Y)) ((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map (AlgebraicGeometry.RingedSpace.inverseImageMap f))).hom.app U = f.hom.c.app U ∧ (AlgebraicGeometry.RingedSpace.toInverseImage f).hom.c.app V = CategoryTheory.CategoryStruct.comp ((AlgebraicGeometry.RingedSpace.inverseImageMap f).hom.app V) ((CategoryTheory.eqToHom ⋯).app V)
```

The ring-sheaf equation, the original presheaf component on every open and
the identity-pushforward transport of the first map.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean#L58) (line 58).

### `Test.InverseImage.sectionMaps`

```lean
theorem Test.InverseImage.sectionMaps {X Y : AlgebraicGeometry.RingedSpace} (f : X ⟶ Y) (U : (TopologicalSpace.Opens ↑↑Y.toPresheafedSpace)ᵒᵖ) (V : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ) : CategoryTheory.CategoryStruct.comp (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).unit.app (AlgebraicGeometry.SheafedSpace.sheaf Y)).hom.app U) (((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map (AlgebraicGeometry.RingedSpace.inverseImageMap f)).hom.app U) = f.hom.c.app U ∧ (AlgebraicGeometry.RingedSpace.toInverseImage f).hom.c.app V = (AlgebraicGeometry.RingedSpace.inverseImageMap f).hom.app V
```

Explicit ring homomorphisms on each target/source open, with the identity transport erased.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean#L77) (line 77).

### `Test.InverseImage.identity`

```lean
theorem Test.InverseImage.identity (X : AlgebraicGeometry.RingedSpace) : CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.toInverseImage (CategoryTheory.CategoryStruct.id X)) (X.ofInverseImage (CategoryTheory.CategoryStruct.id X).hom.base) = CategoryTheory.CategoryStruct.id X
```

Identity morphisms are covered by the same complete full-morphism theorem.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean#L88) (line 88).

### `Test.InverseImage.emptyCarrier`

```lean
theorem Test.InverseImage.emptyCarrier (X : AlgebraicGeometry.RingedSpace) : CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.toInverseImage (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯)) (X.ofInverseImage (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯).hom.base) = AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯
```

The factorization also holds with an empty underlying source.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean#L94) (line 94).

### `Test.InverseImage.zeroRingSpace`

```lean
def Test.InverseImage.zeroRingSpace (T : TopCat) : AlgebraicGeometry.RingedSpace
```

The constant terminal-ring presheaf is a sheaf, including on empty opens.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean#L101) (line 101).

### `Test.InverseImage.zeroRing`

```lean
theorem Test.InverseImage.zeroRing (T : TopCat) : CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.toInverseImage (CategoryTheory.CategoryStruct.id (zeroRingSpace T))) ((zeroRingSpace T).ofInverseImage (CategoryTheory.CategoryStruct.id (zeroRingSpace T)).hom.base) = CategoryTheory.CategoryStruct.id (zeroRingSpace T)
```

Nonzero rings are not needed for a full factorization.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean#L108) (line 108).

### `Test.InverseImage.nonidentityFull`

```lean
theorem Test.InverseImage.nonidentityFull : ∃ (Y : AlgebraicGeometry.RingedSpace) (g : ↑Y.toPresheafedSpace ⟶ ↑Y.toPresheafedSpace), g ≠ CategoryTheory.CategoryStruct.id ↑Y.toPresheafedSpace ∧ (Y.ofInverseImage g).hom.base ≠ CategoryTheory.CategoryStruct.id ↑Y.toPresheafedSpace ∧ CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.toInverseImage (Y.ofInverseImage g)) (Y.ofInverseImage (Y.ofInverseImage g).hom.base) = Y.ofInverseImage g
```

A genuinely nonidentity full map over a constant map of a two-point discrete space.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/InverseImage.lean#L116) (line 116).

## Module `Test.ModuleChangeOfRings`

> # Direct-import change-of-rings clients
>
> These tests exercise maps, naturality, units, counits and sectionwise scalars
> on arbitrary sites, including sites without objects or sections.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean)

### `Test.ModuleChangeOfRings.fullRingNaturality`

```lean
theorem Test.ModuleChangeOfRings.fullRingNaturality {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {U V : Cᵒᵖ} (f : U ⟶ V) (a : ↑(A.obj U)) : (CategoryTheory.ConcreteCategory.hom (theta.app V)) ((CategoryTheory.ConcreteCategory.hom (A.map f)) a) = (CategoryTheory.ConcreteCategory.hom (B.map f)) ((CategoryTheory.ConcreteCategory.hom (theta.app U)) a)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L30) (line 30).

### `Test.ModuleChangeOfRings.nontrivialArrowRestriction`

```lean
theorem Test.ModuleChangeOfRings.nontrivialArrowRestriction {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) {U V : Cᵒᵖ} (f : U ⟶ V) (b : ↑(B.obj U)) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map (RingedSpaces.Modules.tensorPresheaf A B theta M) f)) (b • (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A B theta M U)) m) = (CategoryTheory.ConcreteCategory.hom (B.map f)) b • (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A B theta M V)) ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map M f)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L34) (line 34).

### `Test.ModuleChangeOfRings.tensorMapArbitraryScalar`

```lean
theorem Test.ModuleChangeOfRings.tensorMapArbitraryScalar {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N : RingedSpaces.Modules.Presheaves A} (h : M ⟶ N) (U : Cᵒᵖ) (b : ↑(B.obj U)) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.tensorPresheafFunctor A B theta).map h).app U)) (b • (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A B theta M U)) m) = b • (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A B theta N U)) ((CategoryTheory.ConcreteCategory.hom (h.app U)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L41) (line 41).

### `Test.ModuleChangeOfRings.tensorFunctorIdentityComposition`

```lean
theorem Test.ModuleChangeOfRings.tensorFunctorIdentityComposition {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M N P : RingedSpaces.Modules.Presheaves A} (h : M ⟶ N) (k : N ⟶ P) : (RingedSpaces.Modules.tensorPresheafFunctor A B theta).map (CategoryTheory.CategoryStruct.id M) = CategoryTheory.CategoryStruct.id ((RingedSpaces.Modules.tensorPresheafFunctor A B theta).obj M) ∧ (RingedSpaces.Modules.tensorPresheafFunctor A B theta).map (CategoryTheory.CategoryStruct.comp h k) = CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.tensorPresheafFunctor A B theta).map h) ((RingedSpaces.Modules.tensorPresheafFunctor A B theta).map k)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L48) (line 48).

### `Test.ModuleChangeOfRings.homInverses`

```lean
theorem Test.ModuleChangeOfRings.homInverses {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (N : RingedSpaces.Modules.Presheaves B) (t : RingedSpaces.Modules.tensorPresheaf A B theta M ⟶ N) (g : M ⟶ (PresheafOfModules.restrictScalars (RingedSpaces.Modules.ringMap A B theta)).obj N) : (RingedSpaces.Modules.tensorPresheafHomEquiv A B theta M N).symm ((RingedSpaces.Modules.tensorPresheafHomEquiv A B theta M N) t) = t ∧ (RingedSpaces.Modules.tensorPresheafHomEquiv A B theta M N) ((RingedSpaces.Modules.tensorPresheafHomEquiv A B theta M N).symm g) = g
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L58) (line 58).

### `Test.ModuleChangeOfRings.homNaturalityLeft`

```lean
theorem Test.ModuleChangeOfRings.homNaturalityLeft {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) {M M' : RingedSpaces.Modules.Presheaves A} (h : M ⟶ M') (N : RingedSpaces.Modules.Presheaves B) (t : RingedSpaces.Modules.tensorPresheaf A B theta M' ⟶ N) : RingedSpaces.Modules.tensorPresheafHomDown A B theta M (CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.tensorPresheafFunctor A B theta).map h) t) = CategoryTheory.CategoryStruct.comp h (RingedSpaces.Modules.tensorPresheafHomDown A B theta M' t)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L70) (line 70).

### `Test.ModuleChangeOfRings.homNaturalityRight`

```lean
theorem Test.ModuleChangeOfRings.homNaturalityRight {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) {N N' : RingedSpaces.Modules.Presheaves B} (t : RingedSpaces.Modules.tensorPresheaf A B theta M ⟶ N) (k : N ⟶ N') : RingedSpaces.Modules.tensorPresheafHomDown A B theta M (CategoryTheory.CategoryStruct.comp t k) = CategoryTheory.CategoryStruct.comp (RingedSpaces.Modules.tensorPresheafHomDown A B theta M t) ((PresheafOfModules.restrictScalars (RingedSpaces.Modules.ringMap A B theta)).map k)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L78) (line 78).

### `Test.ModuleChangeOfRings.adjunctionUnitOnSections`

```lean
theorem Test.ModuleChangeOfRings.adjunctionUnitOnSections {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (U : Cᵒᵖ) (m : ↑(PresheafOfModulesOfCommRing.obj M U)) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.tensorPresheafAdjunction A B theta).unit.app M).app U)) m = (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A B theta M U)) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L87) (line 87).

### `Test.ModuleChangeOfRings.adjunctionCounitOnScalars`

```lean
theorem Test.ModuleChangeOfRings.adjunctionCounitOnScalars {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C] (A B : CategoryTheory.Functor Cᵒᵖ CommRingCat) (theta : A ⟶ B) (N : RingedSpaces.Modules.Presheaves B) (U : Cᵒᵖ) (b : ↑(B.obj U)) (n : ↑(PresheafOfModulesOfCommRing.obj N U)) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.tensorPresheafAdjunction A B theta).counit.app N).app U)) (b • (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A B theta ((PresheafOfModules.restrictScalars (RingedSpaces.Modules.ringMap A B theta)).obj N) U)) n) = b • n
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L93) (line 93).

### `Test.ModuleChangeOfRings.zeroRingPresheaf`

```lean
noncomputable def Test.ModuleChangeOfRings.zeroRingPresheaf : CategoryTheory.Functor (Fin 2)ᵒᵖ CommRingCat
```

A literal zero coefficient ring presheaf, without a nontriviality hypothesis.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L120) (line 120).

### `Test.ModuleChangeOfRings.emptySiteAdjunction`

```lean
noncomputable def Test.ModuleChangeOfRings.emptySiteAdjunction (A : CategoryTheory.Functor (CategoryTheory.Discrete PEmpty.{u + 1})ᵒᵖ CommRingCat) : RingedSpaces.Modules.tensorPresheafFunctor A A (CategoryTheory.CategoryStruct.id A) ⊣ PresheafOfModules.restrictScalars (RingedSpaces.Modules.ringMap A A (CategoryTheory.CategoryStruct.id A))
```

The presheaf adjunction also exists when the indexing category is empty.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L134) (line 134).

### `Test.ModuleChangeOfRings.topologicalAdjunction`

```lean
noncomputable def Test.ModuleChangeOfRings.topologicalAdjunction {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) : RingedSpaces.Modules.tensorSheafFunctor A B theta ⊣ SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta)
```

Topological sites infer both sheafification witnesses without hypotheses.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L147) (line 147).

### `Test.ModuleChangeOfRings.sheafUnitGenerator`

```lean
theorem Test.ModuleChangeOfRings.sheafUnitGenerator {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) (M : RingedSpaces.Modules.Sheaves A) (U : (TopologicalSpace.Opens ↑X)ᵒᵖ) (m : ↑(M.val.obj U)) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.tensorSheafAdjunction A B theta).unit.app M).val.app U)) m = (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.moduleSheafificationAdjunction B).unit.app (RingedSpaces.Modules.tensorPresheaf A.obj B.obj theta.hom M.val)).app U)) ((CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A.obj B.obj theta.hom M.val U)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L153) (line 153).

### `Test.ModuleChangeOfRings.sheafCounitGenerator`

```lean
theorem Test.ModuleChangeOfRings.sheafCounitGenerator {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) (N : RingedSpaces.Modules.Sheaves B) (U : (TopologicalSpace.Opens ↑X)ᵒᵖ) (b : ↑(B.obj.obj U)) (n : ↑(N.val.obj U)) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.tensorSheafAdjunction A B theta).counit.app N).val.app U)) ((CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.moduleSheafificationAdjunction B).unit.app (RingedSpaces.Modules.tensorPresheaf A.obj B.obj theta.hom ((SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta)).obj N).val)).app U)) (b • (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A.obj B.obj theta.hom ((SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta)).obj N).val U)) n)) = b • n
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L164) (line 164).

### `Test.ModuleChangeOfRings.sheafHomInverses`

```lean
theorem Test.ModuleChangeOfRings.sheafHomInverses {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) (M : RingedSpaces.Modules.Sheaves A) (N : RingedSpaces.Modules.Sheaves B) (t : (RingedSpaces.Modules.tensorSheafFunctor A B theta).obj M ⟶ N) (g : M ⟶ (SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta)).obj N) : (RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N).symm ((RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N) t) = t ∧ (RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N) ((RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N).symm g) = g
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L179) (line 179).

### `Test.ModuleChangeOfRings.sheafHomOnGenerator`

```lean
theorem Test.ModuleChangeOfRings.sheafHomOnGenerator {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) (M : RingedSpaces.Modules.Sheaves A) (N : RingedSpaces.Modules.Sheaves B) (t : (RingedSpaces.Modules.tensorSheafFunctor A B theta).obj M ⟶ N) (U : (TopologicalSpace.Opens ↑X)ᵒᵖ) (m : ↑(M.val.obj U)) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N) t).val.app U)) m = (CategoryTheory.ConcreteCategory.hom (t.val.app U)) ((CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.moduleSheafificationAdjunction B).unit.app (RingedSpaces.Modules.tensorPresheaf A.obj B.obj theta.hom M.val)).app U)) ((CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A.obj B.obj theta.hom M.val U)) m))
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L192) (line 192).

### `Test.ModuleChangeOfRings.sheafHomNaturalityLeft`

```lean
theorem Test.ModuleChangeOfRings.sheafHomNaturalityLeft {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) {M M' : RingedSpaces.Modules.Sheaves A} (h : M ⟶ M') (N : RingedSpaces.Modules.Sheaves B) (t : (RingedSpaces.Modules.tensorSheafFunctor A B theta).obj M' ⟶ N) : (RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N) (CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.tensorSheafFunctor A B theta).map h) t) = CategoryTheory.CategoryStruct.comp h ((RingedSpaces.Modules.tensorSheafHomEquiv A B theta M' N) t)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L205) (line 205).

### `Test.ModuleChangeOfRings.sheafHomNaturalityRight`

```lean
theorem Test.ModuleChangeOfRings.sheafHomNaturalityRight {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) (M : RingedSpaces.Modules.Sheaves A) {N N' : RingedSpaces.Modules.Sheaves B} (t : (RingedSpaces.Modules.tensorSheafFunctor A B theta).obj M ⟶ N) (k : N ⟶ N') : (RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N') (CategoryTheory.CategoryStruct.comp t k) = CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.tensorSheafHomEquiv A B theta M N) t) ((SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta)).map k)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L214) (line 214).

### `Test.ModuleChangeOfRings.sheafAdjunctionUnitNaturality`

```lean
theorem Test.ModuleChangeOfRings.sheafAdjunctionUnitNaturality {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) {M M' : RingedSpaces.Modules.Sheaves A} (h : M ⟶ M') : CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.tensorSheafAdjunction A B theta).unit.app M) ((SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta)).map ((RingedSpaces.Modules.tensorSheafFunctor A B theta).map h)) = CategoryTheory.CategoryStruct.comp h ((RingedSpaces.Modules.tensorSheafAdjunction A B theta).unit.app M')
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L225) (line 225).

### `Test.ModuleChangeOfRings.sheafAdjunctionCounitNaturality`

```lean
theorem Test.ModuleChangeOfRings.sheafAdjunctionCounitNaturality {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) {N N' : RingedSpaces.Modules.Sheaves B} (k : N ⟶ N') : CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.tensorSheafFunctor A B theta).map ((SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta)).map k)) ((RingedSpaces.Modules.tensorSheafAdjunction A B theta).counit.app N') = CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.tensorSheafAdjunction A B theta).counit.app N) k
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L235) (line 235).

### `Test.ModuleChangeOfRings.emptySpaceAdjunction`

```lean
noncomputable def Test.ModuleChangeOfRings.emptySpaceAdjunction (A B : TopCat.Sheaf CommRingCat ↧PEmpty.{u + 1}) (theta : A ⟶ B) : RingedSpaces.Modules.tensorSheafFunctor A B theta ⊣ SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta)
```

The topological adjunction does not require points in the underlying space.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRings.lean#L247) (line 247).

## Module `Test.ModuleChangeOfRingsAxioms`

> # Transitive axiom audit for module change of rings
>
> The census and generated/private axiom checks use the same `Lean.collectAxioms`
> as `#print axioms`. Explicit references to `_proof_` auxiliaries trigger
> `linter.auxLemma` because those names are unstable; enumerating their actual
> declarations instead keeps this file warning-free without suppressing the linter.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRingsAxioms.lean)

## Module `Test.ModuleChangeOfRingsRoot`

> # Aggregate-import change-of-rings client

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRingsRoot.lean)

### `Test.ModuleChangeOfRingsRoot.scalarRestriction`

```lean
theorem Test.ModuleChangeOfRingsRoot.scalarRestriction (A B : CategoryTheory.Functor (Fin 2)ᵒᵖ CommRingCat) (theta : A ⟶ B) (M : RingedSpaces.Modules.Presheaves A) (b : ↑(B.obj (Opposite.op 1))) (m : ↑(PresheafOfModulesOfCommRing.obj M (Opposite.op 1))) : (CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map (RingedSpaces.Modules.tensorPresheaf A B theta M) (CategoryTheory.homOfLE scalarRestriction._proof_1).op)) (b • (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A B theta M (Opposite.op 1))) m) = (CategoryTheory.ConcreteCategory.hom (B.map (CategoryTheory.homOfLE scalarRestriction._proof_1).op)) b • (CategoryTheory.ConcreteCategory.hom (RingedSpaces.Modules.tensorUnitSection A B theta M (Opposite.op 0))) ((CategoryTheory.ConcreteCategory.hom (PresheafOfModulesOfCommRing.map M (CategoryTheory.homOfLE scalarRestriction._proof_1).op)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRingsRoot.lean#L23) (line 23).

### `Test.ModuleChangeOfRingsRoot.topologicalSheafAdjunction`

```lean
noncomputable def Test.ModuleChangeOfRingsRoot.topologicalSheafAdjunction {X : TopCat} (A B : TopCat.Sheaf CommRingCat X) (theta : A ⟶ B) : RingedSpaces.Modules.tensorSheafFunctor A B theta ⊣ SheafOfModules.restrictScalars (RingedSpaces.Modules.ringSheafMap A B theta)
```

The same-site adjunction inferred from topological sheafification witnesses.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/ModuleChangeOfRingsRoot.lean#L35) (line 35).

## Module `Test.OpenCover`

> # Direct-import clients for ringed-space open-cover gluing
>
> These clients use only the public API, without any access to the construction internals.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/OpenCover.lean)

### `Test.OpenCover.arbitraryFamily`

```lean
theorem Test.OpenCover.arbitraryFamily {X Y : AlgebraicGeometry.RingedSpace} (C : X.OpenCover) (f : (i : C.J) → C.obj i ⟶ Y) (hf : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (C.ι i) (C.ι j)) (f i) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (C.ι i) (C.ι j)) (f j)) : ∃! g : X ⟶ Y, ∀ (i : C.J), CategoryTheory.CategoryStruct.comp (C.ι i) g = f i
```

Existence, actual restrictions, and uniqueness for an arbitrary full-morphism family.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/OpenCover.lean#L26) (line 26).

### `Test.OpenCover.emptyCover`

```lean
def Test.OpenCover.emptyCover (X : AlgebraicGeometry.RingedSpace) : AlgebraicGeometry.RingedSpace.OpenCover (AlgebraicGeometry.SheafedSpace.restrict X ⋯)
```

The empty family covers the empty restriction, even for an arbitrary ringed-space target.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/OpenCover.lean#L36) (line 36).

### `Test.OpenCover.emptyFamily`

```lean
theorem Test.OpenCover.emptyFamily (X Y : AlgebraicGeometry.RingedSpace) : ∃! g : AlgebraicGeometry.SheafedSpace.restrict X ⋯ ⟶ Y, ∀ (i : (emptyCover X).J), CategoryTheory.CategoryStruct.comp ((emptyCover X).ι i) g = i.down.elim
```

The ordinary universal property applies to an empty indexed cover of an empty source.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/OpenCover.lean#L43) (line 43).

### `Test.OpenCover.infiniteCover`

```lean
def Test.OpenCover.infiniteCover (X : AlgebraicGeometry.RingedSpace) : X.OpenCover
```

An infinite-indexed cover whose members away from zero are empty.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/OpenCover.lean#L51) (line 51).

### `Test.OpenCover.infiniteFamily`

```lean
theorem Test.OpenCover.infiniteFamily (X Y : AlgebraicGeometry.RingedSpace) (f : (i : (infiniteCover X).J) → (infiniteCover X).obj i ⟶ Y) (hf : ∀ (i j : (infiniteCover X).J), CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst ((infiniteCover X).ι i) ((infiniteCover X).ι j)) (f i) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd ((infiniteCover X).ι i) ((infiniteCover X).ι j)) (f j)) : ∃! g : X ⟶ Y, ∀ (i : (infiniteCover X).J), CategoryTheory.CategoryStruct.comp ((infiniteCover X).ι i) g = f i
```

The same full-morphism gluing works for an infinite index type with empty members.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/OpenCover.lean#L57) (line 57).

## Module `Test.PresheafInverseImage`

> # Direct-import clients for inverse-image module presheaves
>
> All equations refer to the actual pointwise Kan extensions and their unit.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean)

### `Test.PresheafInverseImage.simultaneousGenerators`

```lean
theorem Test.PresheafInverseImage.simultaneousGenerators {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (U : TopologicalSpace.Opens ↑X) (r : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj (Opposite.op U))) (m : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (Opposite.op U))) : ∃ (i : RingedSpaces.Modules.PresheafInverseImage.index f U) (a : ↑(R.obj (CategoryTheory.CostructuredArrow.left i))) (b : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))), (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp R) i)) a = r ∧ (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) b = m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L28) (line 28).

### `Test.PresheafInverseImage.generatorAction`

```lean
theorem Test.PresheafInverseImage.generatorAction {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (U : TopologicalSpace.Opens ↑X) (i : RingedSpaces.Modules.PresheafInverseImage.index f U) (a : ↑(R.obj (CategoryTheory.CostructuredArrow.left i))) (b : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))) : RingedSpaces.Modules.PresheafInverseImage.pointwiseSmul f R M U ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp R) i)) a) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) b) = (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) (a • b)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L36) (line 36).

### `Test.PresheafInverseImage.ringRestrictionGenerator`

```lean
theorem Test.PresheafInverseImage.ringRestrictionGenerator {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) {U V : TopologicalSpace.Opens ↑X} (g : Opposite.op U ⟶ Opposite.op V) (i : RingedSpaces.Modules.PresheafInverseImage.index f U) (a : ↑(R.obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).map g)) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp R) i)) a) = (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op V)).comp R) ((CategoryTheory.CostructuredArrow.map g).obj i))) a
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L45) (line 45).

### `Test.PresheafInverseImage.moduleRestrictionGenerator`

```lean
theorem Test.PresheafInverseImage.moduleRestrictionGenerator {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {U V : TopologicalSpace.Opens ↑X} (g : Opposite.op U ⟶ Opposite.op V) (i : RingedSpaces.Modules.PresheafInverseImage.index f U) (b : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).map g)) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) b) = (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op V)).comp M.presheaf) ((CategoryTheory.CostructuredArrow.map g).obj i))) b
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L53) (line 53).

### `Test.PresheafInverseImage.restrictionArbitraryScalar`

```lean
theorem Test.PresheafInverseImage.restrictionArbitraryScalar {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {U V : TopologicalSpace.Opens ↑X} (g : Opposite.op U ⟶ Opposite.op V) (r : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj (Opposite.op U))) (m : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).map g)) (r • m) = (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).map g)) r • (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).map g)) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L61) (line 61).

### `Test.PresheafInverseImage.restrictionIdentityComposition`

```lean
theorem Test.PresheafInverseImage.restrictionIdentityComposition {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {U V W : TopologicalSpace.Opens ↑X} (g : Opposite.op U ⟶ Opposite.op V) (h : Opposite.op V ⟶ Opposite.op W) (m : ↑((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).map (CategoryTheory.CategoryStruct.id (Opposite.op U)))) m = m ∧ (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).map (CategoryTheory.CategoryStruct.comp g h))) m = (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).map h)) ((CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).map g)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L71) (line 71).

### `Test.PresheafInverseImage.inducedMapGenerator`

```lean
theorem Test.PresheafInverseImage.inducedMapGenerator {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {N : PresheafOfModules R} (φ : M ⟶ N) (U : TopologicalSpace.Opens ↑X) (i : RingedSpaces.Modules.PresheafInverseImage.index f U) (b : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map φ).app (Opposite.op U))) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) b) = (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp N.presheaf) i)) ((CategoryTheory.ConcreteCategory.hom (φ.app (CategoryTheory.CostructuredArrow.left i))) b)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L81) (line 81).

### `Test.PresheafInverseImage.inducedMapArbitraryScalar`

```lean
theorem Test.PresheafInverseImage.inducedMapArbitraryScalar {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {N : PresheafOfModules R} (φ : M ⟶ N) (U : TopologicalSpace.Opens ↑X) (r : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj (Opposite.op U))) (m : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map φ).app (Opposite.op U))) (r • m) = r • (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map φ).app (Opposite.op U))) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L89) (line 89).

### `Test.PresheafInverseImage.inducedMapNaturality`

```lean
theorem Test.PresheafInverseImage.inducedMapNaturality {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {N : PresheafOfModules R} (φ : M ⟶ N) {U V : TopologicalSpace.Opens ↑X} (g : Opposite.op U ⟶ Opposite.op V) (m : ↑((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map φ).app (Opposite.op V))) ((CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).map g)) m) = (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R N).map g)) ((CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map φ).app (Opposite.op U))) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L99) (line 99).

### `Test.PresheafInverseImage.inducedFunctorLaws`

```lean
theorem Test.PresheafInverseImage.inducedFunctorLaws {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {N P : PresheafOfModules R} (φ : M ⟶ N) (ψ : N ⟶ P) : (RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map (CategoryTheory.CategoryStruct.id M) = CategoryTheory.CategoryStruct.id ((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj M) ∧ (RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map (CategoryTheory.CategoryStruct.comp φ ψ) = CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map φ) ((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map ψ)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L108) (line 108).

### `Test.PresheafInverseImage.actualUnitAction`

```lean
theorem Test.PresheafInverseImage.actualUnitAction {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (V : (TopologicalSpace.Opens ↑Y)ᵒᵖ) (a : ↑(R.obj V)) (b : ↑(M.obj V)) : RingedSpaces.Modules.PresheafInverseImage.pointwiseSmul f R M ((TopologicalSpace.Opens.map f).obj (Opposite.unop V)) ((CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R).app V)) a) ((CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V)) b) = (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V)) (a • b)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L116) (line 116).

### `Test.PresheafInverseImage.actualUnitNaturality`

```lean
theorem Test.PresheafInverseImage.actualUnitNaturality {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {N : PresheafOfModules R} (φ : M ⟶ N) : CategoryTheory.CategoryStruct.comp ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf) ((TopologicalSpace.Opens.map f).op.whiskerLeft (RingedSpaces.Modules.PresheafInverseImage.pointwiseMap f φ)) = CategoryTheory.CategoryStruct.comp ((PresheafOfModules.toPresheaf R).map φ) ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit N.presheaf)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L123) (line 123).

### `Test.PresheafInverseImage.additiveComparisonNatural`

```lean
theorem Test.PresheafInverseImage.additiveComparisonNatural {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {N : PresheafOfModules R} (φ : M ⟶ N) : CategoryTheory.CategoryStruct.comp (RingedSpaces.Modules.PresheafInverseImage.pointwiseMap f φ) ((RingedSpaces.Modules.PresheafInverseImage.underlyingComparison f R).hom.app N) = CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.underlyingComparison f R).hom.app M) ((TopCat.Presheaf.pullback AddCommGrpCat f).map ((PresheafOfModules.toPresheaf R).map φ))
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L130) (line 130).

### `Test.PresheafInverseImage.additiveComparisonUnit`

```lean
theorem Test.PresheafInverseImage.additiveComparisonUnit {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) : CategoryTheory.CategoryStruct.comp ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf) ((TopologicalSpace.Opens.map f).op.whiskerLeft ((RingedSpaces.Modules.PresheafInverseImage.underlyingComparison f R).hom.app M)) = (TopologicalSpace.Opens.map f).op.leftKanExtensionUnit M.presheaf
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImage.lean#L137) (line 137).

## Module `Test.PresheafInverseImageAxioms`

> # Transitive axiom audit for inverse-image module presheaves
>
> The environment census includes private and generated declarations. The same
> `Lean.collectAxioms` mechanism powers `#print axioms`; explicit prints pin the
> public API, all saved clients and selected native dependencies. Enumerating
> generated declarations avoids unstable `_proof_` references in source text.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageAxioms.lean)

## Module `Test.PresheafInverseImageConcrete`

> # Concrete and boundary inverse-image clients
>
> The constant integer module on a two-point discrete space tests a nonidentity
> base map and a restriction to a nonempty proper open. Constant presheaves need
> not satisfy a sheaf condition, even over the empty open.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageConcrete.lean)

## Module `Test.PresheafInverseImageHom`

> # Direct clients for the concrete inverse-image Hom equivalence
>
> These statements use the actual pointwise Kan ring, the accepted module action,
> and mathlib's native module pushforward. The source and target are arbitrary.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean)

### `Test.PresheafInverseImageHom.forwardSection`

```lean
theorem Test.PresheafInverseImageHom.forwardSection {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) (g : (RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj M ⟶ N) (V : (TopologicalSpace.Opens ↑Y)ᵒᵖ) (m : ↑(M.obj V)) : (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.forward f R g).app V)) m = (CategoryTheory.ConcreteCategory.hom (g.app ((TopologicalSpace.Opens.map f).op.obj V))) ((CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V)) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L30) (line 30).

### `Test.PresheafInverseImageHom.descentGenerator`

```lean
theorem Test.PresheafInverseImageHom.descentGenerator {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) (U : TopologicalSpace.Opens ↑X) (i : RingedSpaces.Modules.PresheafInverseImage.index f U) (m : ↑(M.obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.backward f R h).app (Opposite.op U))) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp M.presheaf) i)) m) = (CategoryTheory.ConcreteCategory.hom (N.map (CategoryTheory.CostructuredArrow.hom i))) ((CategoryTheory.ConcreteCategory.hom (h.app (CategoryTheory.CostructuredArrow.left i))) m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L38) (line 38).

### `Test.PresheafInverseImageHom.descentArbitraryScalar`

```lean
theorem Test.PresheafInverseImageHom.descentArbitraryScalar {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) (U : (TopologicalSpace.Opens ↑X)ᵒᵖ) (r : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj U)) (m : ↑(((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj M).obj U)) : (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.backward f R h).app U)) (r • m) = r • (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.backward f R h).app U)) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L47) (line 47).

### `Test.PresheafInverseImageHom.bothHomDirections`

```lean
theorem Test.PresheafInverseImageHom.bothHomDirections {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) (g : (RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj M ⟶ N) (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) : (RingedSpaces.Modules.PresheafInverseImage.homEquiv f R M N).symm ((RingedSpaces.Modules.PresheafInverseImage.homEquiv f R M N) g) = g ∧ (RingedSpaces.Modules.PresheafInverseImage.homEquiv f R M N) ((RingedSpaces.Modules.PresheafInverseImage.homEquiv f R M N).symm h) = h
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L56) (line 56).

### `Test.PresheafInverseImageHom.sourceNaturality`

```lean
theorem Test.PresheafInverseImageHom.sourceNaturality {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) {M' : PresheafOfModules R} (φ : M' ⟶ M) (g : (RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj M ⟶ N) (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) : RingedSpaces.Modules.PresheafInverseImage.forward f R (CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map φ) g) = CategoryTheory.CategoryStruct.comp φ (RingedSpaces.Modules.PresheafInverseImage.forward f R g) ∧ RingedSpaces.Modules.PresheafInverseImage.backward f R (CategoryTheory.CategoryStruct.comp φ h) = CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map φ) (RingedSpaces.Modules.PresheafInverseImage.backward f R h)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L64) (line 64).

### `Test.PresheafInverseImageHom.targetNaturality`

```lean
theorem Test.PresheafInverseImageHom.targetNaturality {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) {N' : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (ψ : N ⟶ N') (g : (RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj M ⟶ N) (h : M ⟶ (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N) : RingedSpaces.Modules.PresheafInverseImage.forward f R (CategoryTheory.CategoryStruct.comp g ψ) = CategoryTheory.CategoryStruct.comp (RingedSpaces.Modules.PresheafInverseImage.forward f R g) ((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map ψ) ∧ RingedSpaces.Modules.PresheafInverseImage.backward f R (CategoryTheory.CategoryStruct.comp h ((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map ψ)) = CategoryTheory.CategoryStruct.comp (RingedSpaces.Modules.PresheafInverseImage.backward f R h) ψ
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L72) (line 72).

### `Test.PresheafInverseImageHom.actualUnitSection`

```lean
theorem Test.PresheafInverseImageHom.actualUnitSection {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (V : (TopologicalSpace.Opens ↑Y)ᵒᵖ) (m : ↑(M.obj V)) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.PresheafInverseImage.adjunction f R).unit.app M).app V)) m = (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V)) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L85) (line 85).

### `Test.PresheafInverseImageHom.actualCounitGenerator`

```lean
theorem Test.PresheafInverseImageHom.actualCounitGenerator {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) (U : TopologicalSpace.Opens ↑X) (i : RingedSpaces.Modules.PresheafInverseImage.index f U) (m : ↑(((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).obj (CategoryTheory.CostructuredArrow.left i))) : (CategoryTheory.ConcreteCategory.hom (((RingedSpaces.Modules.PresheafInverseImage.adjunction f R).counit.app N).app (Opposite.op U))) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι ((CategoryTheory.CostructuredArrow.proj (TopologicalSpace.Opens.map f).op (Opposite.op U)).comp ((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).presheaf) i)) m) = (CategoryTheory.ConcreteCategory.hom (N.map (CategoryTheory.CostructuredArrow.hom i))) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L90) (line 90).

### `Test.PresheafInverseImageHom.actualUnitCounitNaturalities`

```lean
theorem Test.PresheafInverseImageHom.actualUnitCounitNaturalities {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) {M' : PresheafOfModules R} {N' : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)} (φ : M ⟶ M') (ψ : N ⟶ N') : CategoryTheory.CategoryStruct.comp φ ((RingedSpaces.Modules.PresheafInverseImage.adjunction f R).unit.app M') = CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.adjunction f R).unit.app M) (((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).comp (PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R))).map φ) ∧ CategoryTheory.CategoryStruct.comp (((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).comp (RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R)).map ψ) ((RingedSpaces.Modules.PresheafInverseImage.adjunction f R).counit.app N') = CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.adjunction f R).counit.app N) ψ
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L100) (line 100).

### `Test.PresheafInverseImageHom.bothTriangleIdentities`

```lean
theorem Test.PresheafInverseImageHom.bothTriangleIdentities {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) : CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).map ((RingedSpaces.Modules.PresheafInverseImage.adjunction f R).unit.app M)) ((RingedSpaces.Modules.PresheafInverseImage.adjunction f R).counit.app ((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj M)) = CategoryTheory.CategoryStruct.id ((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj ((CategoryTheory.Functor.id (PresheafOfModules R)).obj M)) ∧ CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.adjunction f R).unit.app ((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)) ((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).map ((RingedSpaces.Modules.PresheafInverseImage.adjunction f R).counit.app N)) = CategoryTheory.CategoryStruct.id ((CategoryTheory.Functor.id (PresheafOfModules R)).obj ((PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N))
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L115) (line 115).

### `Test.PresheafInverseImageHom.ordinaryAdditiveTranspose`

```lean
theorem Test.PresheafInverseImageHom.ordinaryAdditiveTranspose {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) (g : (RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj M ⟶ N) : CategoryTheory.CategoryStruct.comp ((PresheafOfModules.toPresheaf R).map (RingedSpaces.Modules.PresheafInverseImage.forward f R g)) ((PresheafOfModules.pushforwardCompToPresheaf ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom = ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv M.presheaf N.presheaf) (CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.underlyingComparison f R).inv.app M) ((PresheafOfModules.toPresheaf ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)).map g))
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHom.lean#L128) (line 128).

## Module `Test.PresheafInverseImageHomAxioms`

> # Compiled-origin axiom census for the inverse-image Hom contribution
>
> Module indices, rather than declaration-name substrings, select every compiled
> constant from the focused leaf and its saved clients. This includes private,
> generated, and names outside their expected namespaces. The audit rejects any
> transitive axiom other than the three permitted foundational axioms.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHomAxioms.lean)

## Module `Test.PresheafInverseImageHomConcrete`

> # Geometric and boundary clients for inverse-image Hom
>
> A constant integer presheaf over the two-point discrete space supplies a
> nonidentity collapse map and a nonempty proper open. No nonzero statement about
> its Kan colimits is inferred from the nonzero input sections.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHomConcrete.lean)

## Module `Test.PresheafInverseImageHomRoot`

> # Aggregate-import clients for inverse-image module-presheaf Hom

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHomRoot.lean)

### `Test.PresheafInverseImageHomRoot.completeHomEquivalence`

```lean
theorem Test.PresheafInverseImageHomRoot.completeHomEquivalence {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) (g : (RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj M ⟶ N) : RingedSpaces.Modules.PresheafInverseImage.backward f R (RingedSpaces.Modules.PresheafInverseImage.forward f R g) = g
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHomRoot.lean#L25) (line 25).

### `Test.PresheafInverseImageHomRoot.actualAdjunction`

```lean
noncomputable def Test.PresheafInverseImageHomRoot.actualAdjunction {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) : RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R ⊣ PresheafOfModules.pushforward ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)
```

The ordinary aggregate import provides the inverse-image/pushforward adjunction.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHomRoot.lean#L30) (line 30).

### `Test.PresheafInverseImageHomRoot.additiveComparison`

```lean
theorem Test.PresheafInverseImageHomRoot.additiveComparison {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (N : PresheafOfModules ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)) (g : (RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).obj M ⟶ N) : CategoryTheory.CategoryStruct.comp ((PresheafOfModules.toPresheaf R).map (RingedSpaces.Modules.PresheafInverseImage.forward f R g)) ((PresheafOfModules.pushforwardCompToPresheaf ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom = ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat f).homEquiv M.presheaf N.presheaf) (CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.underlyingComparison f R).inv.app M) ((PresheafOfModules.toPresheaf ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R)).map g))
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageHomRoot.lean#L36) (line 36).

## Module `Test.PresheafInverseImageLegacyAggregate`

> # Legacy aggregate ordinary-import reduction
>
> This client imports only the aggregate root and independently reconstructs the
> pointwise neighborhood-colimit action without implementation-private names.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageLegacyAggregate.lean)

## Module `Test.PresheafInverseImageNativeDirect`

> # Ordinary native import of the pointwise module action
>
> The expected action is constructed independently from the exposed neighborhood
> diagrams and Kan-colimit comparisons, without access to implementation helpers.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageNativeDirect.lean)

## Module `Test.PresheafInverseImageRoot`

> # Aggregate-import clients for inverse-image module presheaves

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageRoot.lean)

### `Test.PresheafInverseImageRoot.arbitraryScalarRestriction`

```lean
theorem Test.PresheafInverseImageRoot.arbitraryScalarRestriction {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) {U V : TopologicalSpace.Opens ↑X} (g : Opposite.op U ⟶ Opposite.op V) (r : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).obj (Opposite.op U))) (m : ↑(((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension M.presheaf).obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).map g)) (r • m) = (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R).map g)) r • (CategoryTheory.ConcreteCategory.hom ((RingedSpaces.Modules.PresheafInverseImage.inverseImageModule f R M).map g)) m
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageRoot.lean#L26) (line 26).

### `Test.PresheafInverseImageRoot.actualUnit`

```lean
theorem Test.PresheafInverseImageRoot.actualUnit {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) (V : (TopologicalSpace.Opens ↑Y)ᵒᵖ) (r : ↑(R.obj V)) (m : ↑(M.obj V)) : RingedSpaces.Modules.PresheafInverseImage.pointwiseSmul f R M ((TopologicalSpace.Opens.map f).obj (Opposite.unop V)) ((CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit R).app V)) r) ((CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V)) m) = (CategoryTheory.ConcreteCategory.hom (((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V)) (r • m)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageRoot.lean#L36) (line 36).

### `Test.PresheafInverseImageRoot.fullUnderlyingIso`

```lean
theorem Test.PresheafInverseImageRoot.fullUnderlyingIso {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) : CategoryTheory.CategoryStruct.comp ((RingedSpaces.Modules.PresheafInverseImage.underlyingComparison f R).hom.app M) ((RingedSpaces.Modules.PresheafInverseImage.underlyingComparison f R).inv.app M) = CategoryTheory.CategoryStruct.id (((RingedSpaces.Modules.PresheafInverseImage.inverseImageFunctor f R).comp (PresheafOfModules.toPresheaf ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtension R))).obj M)
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageRoot.lean#L43) (line 43).

### `Test.PresheafInverseImageRoot.additiveUnitComparison`

```lean
theorem Test.PresheafInverseImageRoot.additiveUnitComparison {X Y : TopCat} (f : X ⟶ Y) (R : TopCat.Presheaf RingCat Y) (M : PresheafOfModules R) : CategoryTheory.CategoryStruct.comp ((TopologicalSpace.Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf) ((TopologicalSpace.Opens.map f).op.whiskerLeft ((RingedSpaces.Modules.PresheafInverseImage.underlyingComparison f R).hom.app M)) = (TopologicalSpace.Opens.map f).op.leftKanExtensionUnit M.presheaf
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/PresheafInverseImageRoot.lean#L50) (line 50).

## Module `Test.Restriction`

> # Direct-import clients for literal open-intersection gluing
>
> These checks use full ringed-space morphisms through the public restriction, pullback
> and gluing APIs, without the private lifting implementation.

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean)

### `Test.Restriction.literalInclusion`

```lean
theorem Test.Restriction.literalInclusion {X : AlgebraicGeometry.RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) (h : U ≤ V) (t : ↥U) : (CategoryTheory.ConcreteCategory.hom (AlgebraicGeometry.RingedSpace.restrictMap U V h).hom.base) t = ⟨↑t, ⋯⟩
```

The restriction map is the literal inclusion on underlying points.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L29) (line 29).

### `Test.Restriction.identityRestriction`

```lean
theorem Test.Restriction.identityRestriction {X : AlgebraicGeometry.RingedSpace} (U : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) : AlgebraicGeometry.RingedSpace.restrictMap U U ⋯ = CategoryTheory.CategoryStruct.id (AlgebraicGeometry.SheafedSpace.restrict X ⋯)
```

Restriction along an identity inclusion is the identity full morphism.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L34) (line 34).

### `Test.Restriction.composedRestriction`

```lean
theorem Test.Restriction.composedRestriction {X : AlgebraicGeometry.RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) {W : TopologicalSpace.Opens ↑↑X.toPresheafedSpace} (hUV : U ≤ V) (hVW : V ≤ W) : CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap U V hUV) (AlgebraicGeometry.RingedSpace.restrictMap V W hVW) = AlgebraicGeometry.RingedSpace.restrictMap U W ⋯
```

The full restriction maps are functorial along chains of inclusions.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L39) (line 39).

### `Test.Restriction.fullFactorization`

```lean
theorem Test.Restriction.fullFactorization {X : AlgebraicGeometry.RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) (h : U ≤ V) : CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap U V h) (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯) = AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯
```

The factorization is an equality of full morphisms, not merely continuous maps.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L45) (line 45).

### `Test.Restriction.sheafComponent`

```lean
theorem Test.Restriction.sheafComponent {X : AlgebraicGeometry.RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) (h : U ≤ V) : (CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap U V h) (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯)).hom = (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯).hom
```

The factorization agrees even as a presheafed-space morphism, so in particular
its structure-sheaf transformation is not merely inferred from the carrier map.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L51) (line 51).

### `Test.Restriction.literalPullback`

```lean
theorem Test.Restriction.literalPullback {X : AlgebraicGeometry.RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) : CategoryTheory.IsPullback (AlgebraicGeometry.RingedSpace.restrictMap (U ⊓ V) U ⋯) (AlgebraicGeometry.RingedSpace.restrictMap (U ⊓ V) V ⋯) (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯) (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯)
```

The literal intersection is a categorical pullback as a full ringed space.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L58) (line 58).

### `Test.Restriction.literalProjectionLeft`

```lean
theorem Test.Restriction.literalProjectionLeft {X : AlgebraicGeometry.RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) : CategoryTheory.CategoryStruct.comp ⋯.isoPullback.hom (CategoryTheory.Limits.pullback.fst (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯) (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯)) = AlgebraicGeometry.RingedSpace.restrictMap (U ⊓ V) U ⋯
```

Pullback comparison genuinely identifies both full projections.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L66) (line 66).

### `Test.Restriction.literalProjectionRight`

```lean
theorem Test.Restriction.literalProjectionRight {X : AlgebraicGeometry.RingedSpace} (U V : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) : CategoryTheory.CategoryStruct.comp ⋯.isoPullback.hom (CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯) (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯)) = AlgebraicGeometry.RingedSpace.restrictMap (U ⊓ V) V ⋯
```

*No declaration docstring is attached in the native record.*

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L73) (line 73).

### `Test.Restriction.emptyIntersection`

```lean
theorem Test.Restriction.emptyIntersection {X : AlgebraicGeometry.RingedSpace} (U : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) : CategoryTheory.IsPullback (AlgebraicGeometry.RingedSpace.restrictMap (⊥ ⊓ U) ⊥ ⋯) (AlgebraicGeometry.RingedSpace.restrictMap (⊥ ⊓ U) U ⋯) (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯) (AlgebraicGeometry.SheafedSpace.ofRestrict X ⋯)
```

The empty literal intersection is still a full categorical pullback.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L79) (line 79).

### `Test.Restriction.pullbackToLiteral`

```lean
theorem Test.Restriction.pullbackToLiteral {X Y : AlgebraicGeometry.RingedSpace} (C : X.OpenCover) (f : (i : C.J) → C.obj i ⟶ Y) (h : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (C.ι i) (C.ι j)) (f i) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (C.ι i) (C.ι j)) (f j)) (i j : C.J) : CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U i) ⋯) (f i) = CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U j) ⋯) (f j)
```

A downstream client converts the categorical condition to literal intersections.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L89) (line 89).

### `Test.Restriction.literalToPullback`

```lean
theorem Test.Restriction.literalToPullback {X Y : AlgebraicGeometry.RingedSpace} (C : X.OpenCover) (f : (i : C.J) → C.obj i ⟶ Y) (h : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U i) ⋯) (f i) = CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U j) ⋯) (f j)) (i j : C.J) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (C.ι i) (C.ι j)) (f i) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (C.ι i) (C.ι j)) (f j)
```

The converse converts literal intersection agreement to categorical compatibility.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L97) (line 97).

### `Test.Restriction.uniqueLiteralExtension`

```lean
theorem Test.Restriction.uniqueLiteralExtension {X Y : AlgebraicGeometry.RingedSpace} (C : X.OpenCover) (f : (i : C.J) → C.obj i ⟶ Y) (h : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U i) ⋯) (f i) = CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U j) ⋯) (f j)) : ∃! g : X ⟶ Y, ∀ (i : C.J), CategoryTheory.CategoryStruct.comp (C.ι i) g = f i
```

Unique full extension from literal intersection compatibility.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L105) (line 105).

### `Test.Restriction.emptyCoverLiteral`

```lean
theorem Test.Restriction.emptyCoverLiteral (X Y : AlgebraicGeometry.RingedSpace) : ∃! g : AlgebraicGeometry.SheafedSpace.restrict X ⋯ ⟶ Y, ∀ (i : (OpenCover.emptyCover X).J), CategoryTheory.CategoryStruct.comp ((OpenCover.emptyCover X).ι i) g = i.down.elim
```

Vacuous compatibility glues the empty cover of the empty restriction.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L112) (line 112).

### `Test.Restriction.infiniteCoverLiteral`

```lean
theorem Test.Restriction.infiniteCoverLiteral (X Y : AlgebraicGeometry.RingedSpace) (f : (i : (OpenCover.infiniteCover X).J) → (OpenCover.infiniteCover X).obj i ⟶ Y) (h : ∀ (i j : (OpenCover.infiniteCover X).J), CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap ((OpenCover.infiniteCover X).U i ⊓ (OpenCover.infiniteCover X).U j) ((OpenCover.infiniteCover X).U i) ⋯) (f i) = CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap ((OpenCover.infiniteCover X).U i ⊓ (OpenCover.infiniteCover X).U j) ((OpenCover.infiniteCover X).U j) ⋯) (f j)) : ∃! g : X ⟶ Y, ∀ (i : (OpenCover.infiniteCover X).J), CategoryTheory.CategoryStruct.comp ((OpenCover.infiniteCover X).ι i) g = f i
```

An infinite indexed cover with empty members still uses literal intersections.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Restriction.lean#L122) (line 122).

## Module `Test.Root`

> # Aggregate-import client

[Module source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Root.lean)

### `Test.Root.gluing`

```lean
theorem Test.Root.gluing {X Y : AlgebraicGeometry.RingedSpace} (C : X.OpenCover) (f : (i : C.J) → C.obj i ⟶ Y) (hf : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst (C.ι i) (C.ι j)) (f i) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd (C.ι i) (C.ι j)) (f j)) : ∃! g : X ⟶ Y, ∀ (i : C.J), CategoryTheory.CategoryStruct.comp (C.ι i) g = f i
```

A downstream client needs only the aggregate import for the full universal property.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Root.lean#L22) (line 22).

### `Test.Root.literalGluing`

```lean
theorem Test.Root.literalGluing {X Y : AlgebraicGeometry.RingedSpace} (C : X.OpenCover) (f : (i : C.J) → C.obj i ⟶ Y) (hf : ∀ (i j : C.J), CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U i) ⋯) (f i) = CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.restrictMap (C.U i ⊓ C.U j) (C.U j) ⋯) (f j)) : ∃! g : X ⟶ Y, ∀ (i : C.J), CategoryTheory.CategoryStruct.comp (C.ι i) g = f i
```

Aggregate-import client: both compatibility directions and unique literal gluing.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Root.lean#L30) (line 30).

### `Test.Root.inverseImageFull`

```lean
theorem Test.Root.inverseImageFull {X Y : AlgebraicGeometry.RingedSpace} (f : X ⟶ Y) : CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.RingedSpace.toInverseImage f) (Y.ofInverseImage f.hom.base) = f ∧ (AlgebraicGeometry.RingedSpace.toInverseImage f).hom.base = CategoryTheory.CategoryStruct.id ↑X.toPresheafedSpace
```

An aggregate-only client obtains the full factorization for every full morphism.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Root.lean#L44) (line 44).

### `Test.Root.inverseImageContinuous`

```lean
theorem Test.Root.inverseImageContinuous (Y : AlgebraicGeometry.RingedSpace) {T : TopCat} (g : T ⟶ ↑Y.toPresheafedSpace) : ↑(Y.inverseImage g).toPresheafedSpace = T ∧ AlgebraicGeometry.SheafedSpace.sheaf (Y.inverseImage g) = (TopCat.Sheaf.pullback CommRingCat g).obj (AlgebraicGeometry.SheafedSpace.sheaf Y) ∧ (Y.ofInverseImage g).hom.base = g
```

The aggregate also constructs the actual sheaf from an arbitrary continuous map.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Root.lean#L50) (line 50).

### `Test.Root.inverseImageSections`

```lean
theorem Test.Root.inverseImageSections {X Y : AlgebraicGeometry.RingedSpace} (f : X ⟶ Y) (U : (TopologicalSpace.Opens ↑↑Y.toPresheafedSpace)ᵒᵖ) : CategoryTheory.CategoryStruct.comp ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).unit.app (AlgebraicGeometry.SheafedSpace.sheaf Y)) ((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map (AlgebraicGeometry.RingedSpace.inverseImageMap f)) = CategoryTheory.Sheaf.homEquiv.symm f.hom.c ∧ CategoryTheory.CategoryStruct.comp (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.hom.base).unit.app (AlgebraicGeometry.SheafedSpace.sheaf Y)).hom.app U) (((TopCat.Sheaf.pushforward CommRingCat f.hom.base).map (AlgebraicGeometry.RingedSpace.inverseImageMap f)).hom.app U) = f.hom.c.app U
```

The aggregate exposes both the full sheaf mate equation and every-open ring maps.

[Source](https://github.com/FormalFrontier/ringed-spaces/blob/958b340be6cf1a0bc86c2c378352664c9f7cca62/Test/Root.lean#L60) (line 60).
