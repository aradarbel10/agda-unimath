---
title: endomorphisms
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.endomorphisms where

open import foundation-core.endomorphisms public

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (id; _∘_)
open import foundation.identity-types using (refl)
open import foundation.sets using
  ( Set; type-Set; is-set; is-set-function-type; is-set-type-Set)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU)

open import group-theory.monoids using (Monoid)
open import group-theory.semigroups using (Semigroup)

open import structured-types.pointed-types
open import structured-types.wild-monoids
```

## Idea

An endomorphism on a type `A` is a map `A → A`.

## Definitions

### Endomorphisms

```agda
endo-Wild-Monoid : {l : Level} → UU l → Wild-Monoid l
pr1 (pr1 (endo-Wild-Monoid X)) = endo-Pointed-Type X
pr1 (pr2 (pr1 (endo-Wild-Monoid X))) g f = g ∘ f
pr1 (pr2 (pr2 (pr1 (endo-Wild-Monoid X)))) f = refl
pr1 (pr2 (pr2 (pr2 (pr1 (endo-Wild-Monoid X))))) f = refl
pr2 (pr2 (pr2 (pr2 (pr1 (endo-Wild-Monoid X))))) = refl
pr1 (pr2 (endo-Wild-Monoid X)) h g f = refl
pr1 (pr2 (pr2 (endo-Wild-Monoid X))) g f = refl
pr1 (pr2 (pr2 (pr2 (endo-Wild-Monoid X)))) g f = refl
pr1 (pr2 (pr2 (pr2 (pr2 (endo-Wild-Monoid X))))) g f = refl
pr2 (pr2 (pr2 (pr2 (pr2 (endo-Wild-Monoid X))))) = star

endo-Semigroup : {l : Level} → Set l → Semigroup l
pr1 (endo-Semigroup X) = endo-Set X
pr1 (pr2 (endo-Semigroup X)) g f = g ∘ f
pr2 (pr2 (endo-Semigroup X)) h g f = refl

endo-Monoid : {l : Level} → Set l → Monoid l
pr1 (endo-Monoid X) = endo-Semigroup X
pr1 (pr2 (endo-Monoid X)) = id
pr1 (pr2 (pr2 (endo-Monoid X))) f = refl
pr2 (pr2 (pr2 (endo-Monoid X))) f = refl
```
