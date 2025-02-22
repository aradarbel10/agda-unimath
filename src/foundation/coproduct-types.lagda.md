---
title: Coproduct types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.coproduct-types where

open import foundation.contractible-types using
  ( is-contr; eq-is-contr; center)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso; empty-Prop)
open import foundation.equivalences using (_≃_; is-equiv-has-inverse)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (_＝_; refl; ap)
open import foundation.injective-maps using (is-injective)
open import foundation.negation using (¬)
open import foundation.noncontractible-types using (is-not-contractible)
open import foundation.propositions using
  ( all-elements-equal; is-prop; is-prop-all-elements-equal; eq-is-prop';
    Prop; type-Prop; is-prop-type-Prop)
open import foundation.unit-type using (star; unit-Prop)
open import foundation.universe-levels using (Level; lzero; _⊔_; UU)
```

## Idea

The coproduct of two types `A` and `B` can be thought of as the disjoint union of `A` and `B`. 

## Definition

### Coproducts

```agda
data _+_ {l1 l2 : Level} (A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)  where
  inl : A → A + B
  inr : B → A + B
  
ind-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A + B → UU l3) →
  ((x : A) → C (inl x)) → ((y : B) → C (inr y)) →
  (t : A + B) → C t
ind-coprod C f g (inl x) = f x
ind-coprod C f g (inr x) = g x
```

### The predicates of being in the left and in the right summand

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where
  
  is-left-Prop : X + Y → Prop lzero
  is-left-Prop (inl x) = unit-Prop
  is-left-Prop (inr x) = empty-Prop

  is-left : X + Y → UU lzero
  is-left x = type-Prop (is-left-Prop x)

  is-prop-is-left : (x : X + Y) → is-prop (is-left x)
  is-prop-is-left x = is-prop-type-Prop (is-left-Prop x)

  is-right-Prop : X + Y → Prop lzero
  is-right-Prop (inl x) = empty-Prop
  is-right-Prop (inr x) = unit-Prop

  is-right : X + Y → UU lzero
  is-right x = type-Prop (is-right-Prop x)

  is-prop-is-right : (x : X + Y) → is-prop (is-right x)
  is-prop-is-right x = is-prop-type-Prop (is-right-Prop x)
```

## Properties

### The left and right inclusions are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-inl : is-injective {B = A + B} inl
  is-injective-inl refl = refl

  is-injective-inr : is-injective {B = A + B} inr
  is-injective-inr refl = refl 

  neq-inl-inr : {x : A} {y : B} → ¬ (inl x ＝ inr y)
  neq-inl-inr ()

  neq-inr-inl : {x : B} {y : A} → ¬ (inr x ＝ inl y)
  neq-inr-inl ()
```

### The type of left elements is equivalent to the left summand

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  map-equiv-left-summand : Σ (X + Y) is-left → X
  map-equiv-left-summand (pair (inl x) star) = x
  map-equiv-left-summand (pair (inr x) ())

  map-inv-equiv-left-summand : X → Σ (X + Y) is-left
  map-inv-equiv-left-summand x = pair (inl x) star

  issec-map-inv-equiv-left-summand :
    (map-equiv-left-summand ∘ map-inv-equiv-left-summand) ~ id
  issec-map-inv-equiv-left-summand x = refl

  isretr-map-inv-equiv-left-summand :
    (map-inv-equiv-left-summand ∘ map-equiv-left-summand) ~ id
  isretr-map-inv-equiv-left-summand (pair (inl x) star) = refl
  isretr-map-inv-equiv-left-summand (pair (inr x) ())
  
  equiv-left-summand : (Σ (X + Y) is-left) ≃ X
  pr1 equiv-left-summand = map-equiv-left-summand
  pr2 equiv-left-summand =
    is-equiv-has-inverse
      map-inv-equiv-left-summand
      issec-map-inv-equiv-left-summand
      isretr-map-inv-equiv-left-summand
```

### The type of right elements is equivalent to the right summand

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  map-equiv-right-summand : Σ (X + Y) is-right → Y
  map-equiv-right-summand (pair (inl x) ())
  map-equiv-right-summand (pair (inr x) star) = x

  map-inv-equiv-right-summand : Y → Σ (X + Y) is-right
  map-inv-equiv-right-summand y = pair (inr y) star

  issec-map-inv-equiv-right-summand :
    (map-equiv-right-summand ∘ map-inv-equiv-right-summand) ~ id
  issec-map-inv-equiv-right-summand y = refl

  isretr-map-inv-equiv-right-summand :
    (map-inv-equiv-right-summand ∘ map-equiv-right-summand) ~ id
  isretr-map-inv-equiv-right-summand (pair (inl x) ())
  isretr-map-inv-equiv-right-summand (pair (inr x) star) = refl
  
  equiv-right-summand : (Σ (X + Y) is-right) ≃ Y
  pr1 equiv-right-summand = map-equiv-right-summand
  pr2 equiv-right-summand =
    is-equiv-has-inverse
      map-inv-equiv-right-summand
      issec-map-inv-equiv-right-summand
      isretr-map-inv-equiv-right-summand
```

### Coproducts of contractible types are not contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-not-contractible-coprod-is-contr :
      is-contr A → is-contr B → is-not-contractible (A + B)
    is-not-contractible-coprod-is-contr HA HB HAB =
      neq-inl-inr {x = center HA} {y = center HB} (eq-is-contr  HAB)
```

### Coproducts of mutually exclusive propositions are propositions

```agda
module _
  {l1 l2 : Level} {P : UU l1} {Q : UU l2}
  where

  abstract
    all-elements-equal-coprod :
      (P → ¬ Q) → all-elements-equal P → all-elements-equal Q →
      all-elements-equal (P + Q)
    all-elements-equal-coprod f is-prop-P is-prop-Q (inl p) (inl p') =
      ap inl (is-prop-P p p')
    all-elements-equal-coprod f is-prop-P is-prop-Q (inl p) (inr q') =
      ex-falso (f p q')
    all-elements-equal-coprod f is-prop-P is-prop-Q (inr q) (inl p') =
      ex-falso (f p' q)
    all-elements-equal-coprod f is-prop-P is-prop-Q (inr q) (inr q') =
      ap inr (is-prop-Q q q')
  
  abstract
    is-prop-coprod : (P → ¬ Q) → is-prop P → is-prop Q → is-prop (P + Q)
    is-prop-coprod f is-prop-P is-prop-Q =
      is-prop-all-elements-equal
        ( all-elements-equal-coprod f
          ( eq-is-prop' is-prop-P)
          ( eq-is-prop' is-prop-Q))

coprod-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  (type-Prop P → ¬ (type-Prop Q)) → Prop (l1 ⊔ l2)
pr1 (coprod-Prop P Q H) = type-Prop P + type-Prop Q
pr2 (coprod-Prop P Q H) =
  is-prop-coprod H (is-prop-type-Prop P) (is-prop-type-Prop Q)
```
