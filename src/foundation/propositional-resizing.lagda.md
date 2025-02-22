---
title: Propositional resizing
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.propositional-resizing where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

## Idea

We say that there is propositional resizing for propositions of universe levels `l1` and `l2` if there is a type `Ω : UU l1` equipped with a subtype `Q` such that for each proposition `P` of universe level l2` there is an element `u : Ω` such that `Q u ≃ P`.

## Definition

```agda
propositional-resizing : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
propositional-resizing l1 l2 =
  Σ ( Σ (UU l1) (subtype l1))
    ( λ Ω → ( P : Prop l2) → Σ (pr1 Ω) (λ u → type-equiv-Prop (pr2 Ω u) P))
```
