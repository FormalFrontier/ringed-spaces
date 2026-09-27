<!-- SPDX-License-Identifier: Apache-2.0 -->

# Ringed-space module square pasting

Import `RingedSpaces` for the public aggregate, or
`RingedSpaces.Modules.BaseChangePasting` for the narrower leaf. Both expose
the **actual** `RingedSpaces.Modules.BaseChange.pushPull` comparison for
arbitrary commutative squares of full ringed-space morphisms. Here `L` is
sheafified coefficient-changing inverse image, `R` is full direct image,
and `A` is their actual adjunction. Their canonical composition isomorphisms
come from `RingedSpaces.Modules.PullbackCoherence`.

* `BaseChange.pushPull_pastePullback` composes squares left to right:

  ```text
  W₀ ─a₀₁→ W₁ ─a₁₂→ W₂
  │v₀       │v₁       │v₂
  Z₀ ─b₀₁→ Z₁ ─b₁₂→ Z₂
  ```

  The result expands `L (b₀₁ ≫ b₁₂)` through `pullbackComp.inv`, applies
  the right square's mate followed by the left square's mate, then contracts
  `L a₁₂ ⋙ L a₀₁` through `pullbackComp.hom`.

* `BaseChange.pushPull_pastePushforward` composes squares top to bottom:

  ```text
  W₀ ─a₀→ X₀
  │v₀      │w₀
  W₁ ─a₁→ X₁
  │v₁      │w₁
  W₂ ─a₂→ X₂
  ```

  The result expands `R (w₀ ≫ w₁)` through `pushforwardComp.inv`, applies
  the lower mate followed by the upper mate, then contracts `R v₀ ⋙ R v₁`
  through `pushforwardComp.hom`.

Both are equalities of natural transformations with explicit functor
associators, not strict identifications of functors. Only the two constituent
square-commutativity equalities are assumed: no Cartesian, flatness, nonzero,
invertibility, or raw-tensor-section condition is required. The proofs use
mathlib's `mateEquiv_vcomp` and `mateEquiv_hcomp` and the existing composition
coherence of the actual functors. The public client
[`Test/RingedSpaceBaseChangePasting.lean`](../Test/RingedSpaceBaseChangePasting.lean)
checks both arbitrary-square laws and the non-Cartesian empty-corner example,
using the explicit existing fixture import `Test.RingedSpaceBaseChange`.

The mathematical leaf originated with formalization-worker-b, Hive Task
`hive-request-7b88f0e919ceb77be172b73736ccdc7f3ff43ad5`
(UID `e330b828-529f-49c8-b2e0-e07909c10cef`). This guide describes the
API regardless of its release stage; destination review, owner acceptance,
official publication and source-coverage acceptance are separate recorded
decisions, none certified by this guide alone.
