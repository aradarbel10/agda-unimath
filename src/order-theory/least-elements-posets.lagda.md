# Least elements in posets

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.least-elements-posets where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using
  ( Prop; is-prop; all-elements-equal; is-prop-all-elements-equal)
open import foundation.subtypes using (eq-type-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import order-theory.least-elements-preorders using
  ( is-least-element-preorder-Prop; is-least-element-Preorder;
    is-prop-is-least-element-Preorder; least-element-Preorder)
open import order-theory.posets using
  ( Poset; element-Poset; preorder-Poset; antisymmetric-leq-Poset)
```

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-least-element-poset-Prop : element-Poset X → Prop (l1 ⊔ l2)
  is-least-element-poset-Prop =
    is-least-element-preorder-Prop (preorder-Poset X)

  is-least-element-Poset : element-Poset X → UU (l1 ⊔ l2)
  is-least-element-Poset = is-least-element-Preorder (preorder-Poset X)

  is-prop-is-least-element-Poset :
    (x : element-Poset X) → is-prop (is-least-element-Poset x)
  is-prop-is-least-element-Poset =
    is-prop-is-least-element-Preorder (preorder-Poset X)

  least-element-Poset : UU (l1 ⊔ l2)
  least-element-Poset = least-element-Preorder (preorder-Poset X)

  all-elements-equal-least-element-Poset :
    all-elements-equal least-element-Poset
  all-elements-equal-least-element-Poset (pair x H) (pair y K) =
    eq-type-subtype
      ( is-least-element-poset-Prop)
      ( antisymmetric-leq-Poset X x y (H y) (K x))

  is-prop-least-element-Poset : is-prop least-element-Poset
  is-prop-least-element-Poset =
    is-prop-all-elements-equal all-elements-equal-least-element-Poset

  has-least-element-poset-Prop : Prop (l1 ⊔ l2)
  pr1 has-least-element-poset-Prop = least-element-Poset
  pr2 has-least-element-poset-Prop = is-prop-least-element-Poset
```
