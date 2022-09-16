---
title: Vectors on rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.vectors-on-rings where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.coproduct-types using (inl; inr)
open import foundation.identity-types using (Id; _＝_; refl; ap; ap-binary; _∙_; inv)
open import foundation.equational-reasoning
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU)

open import linear-algebra.constant-vectors using (constant-vec)
open import linear-algebra.functoriality-vectors using
  ( map-binary-vec; htpy-vec; map-vec)
open import linear-algebra.scalar-multiplication-vectors using (scalar-mul-vec)
open import linear-algebra.vectors using
  ( vec; empty-vec; _∷_; head-vec; tail-vec)

open import ring-theory.rings using
  ( Ring; type-Ring; add-Ring; zero-Ring; left-unit-law-add-Ring;
    right-unit-law-add-Ring; neg-Ring; associative-add-Ring;
    left-inverse-law-add-Ring; right-inverse-law-add-Ring; mul-Ring;
    left-unit-law-mul-Ring; right-unit-law-mul-Ring;
    left-zero-law-mul-Ring; right-zero-law-mul-Ring;
    associative-mul-Ring; one-Ring;
    commutative-add-Ring;
    left-distributive-mul-add-Ring; right-distributive-mul-add-Ring)

open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

Given a ring `R`, the type `vec n R` of `R`-vectors is an `R`-module

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where
  
  vec-Ring : ℕ → UU l
  vec-Ring = vec (type-Ring R)

  head-vec-Ring : {n : ℕ} → vec-Ring (succ-ℕ n) → type-Ring R
  head-vec-Ring v = head-vec v

  tail-vec-Ring : {n : ℕ} → vec-Ring (succ-ℕ n) → vec-Ring n
  tail-vec-Ring v = tail-vec v
```

### Zero vector on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-vec-Ring : {n : ℕ} → vec-Ring R n
  zero-vec-Ring {n} = constant-vec (zero-Ring R)
```

### Pointwise addition of vectors on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-vec-Ring : {n : ℕ} → vec-Ring R n → vec-Ring R n → vec-Ring R n
  add-vec-Ring = map-binary-vec (add-Ring R)

  left-unit-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (add-vec-Ring (zero-vec-Ring R) v) v
  left-unit-law-add-vec-Ring empty-vec = refl
  left-unit-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-add-Ring R x)
      ( left-unit-law-add-vec-Ring v)

  right-unit-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (add-vec-Ring v (zero-vec-Ring R)) v
  right-unit-law-add-vec-Ring empty-vec = refl
  right-unit-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-add-Ring R x)
      ( right-unit-law-add-vec-Ring v)

  associative-add-vec-Ring :
    {n : ℕ} (v1 v2 v3 : vec-Ring R n) →
    Id ( add-vec-Ring (add-vec-Ring v1 v2) v3)
       ( add-vec-Ring v1 (add-vec-Ring v2 v3))
  associative-add-vec-Ring empty-vec empty-vec empty-vec = refl
  associative-add-vec-Ring (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-add-Ring R x y z)
      ( associative-add-vec-Ring v1 v2 v3)

  commutative-add-vec-Ring :
    {n : ℕ} (v w : vec-Ring R n) → Id (add-vec-Ring v w) (add-vec-Ring w v)
  commutative-add-vec-Ring empty-vec empty-vec = refl
  commutative-add-vec-Ring (x ∷ v) (y ∷ w) =
    ap-binary _∷_
      ( commutative-add-Ring R x y)
      ( commutative-add-vec-Ring v w)
```

### The negative of a vector on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-vec-Ring : {n : ℕ} → vec-Ring R n → vec-Ring R n
  neg-vec-Ring = map-vec (neg-Ring R)

  left-inverse-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) →
    Id (add-vec-Ring R (neg-vec-Ring v) v) (zero-vec-Ring R)
  left-inverse-law-add-vec-Ring empty-vec = refl
  left-inverse-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-inverse-law-add-Ring R x)
      ( left-inverse-law-add-vec-Ring v)

  right-inverse-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) →
    Id (add-vec-Ring R v (neg-vec-Ring v)) (zero-vec-Ring R)
  right-inverse-law-add-vec-Ring empty-vec = refl
  right-inverse-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-inverse-law-add-Ring R x)
      ( right-inverse-law-add-vec-Ring v)
```

### Scalar multiplication of vectors on rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-scalar-mul-vec-Ring : {n : ℕ} (r : type-Ring R) → vec-Ring R n → vec-Ring R n
  left-scalar-mul-vec-Ring r empty-vec = empty-vec
  left-scalar-mul-vec-Ring r (x ∷ v) = mul-Ring R r x ∷ left-scalar-mul-vec-Ring r v

  right-scalar-mul-vec-Ring : {n : ℕ} → vec-Ring R n → type-Ring R → vec-Ring R n
  right-scalar-mul-vec-Ring empty-vec r = empty-vec
  right-scalar-mul-vec-Ring (x ∷ v) r = mul-Ring R x r ∷ right-scalar-mul-vec-Ring v r

  associative-left-scalar-mul-vec-Ring :
    {n : ℕ} (r s : type-Ring R) (v : vec-Ring R n) →
    Id ( left-scalar-mul-vec-Ring (mul-Ring R r s) v)
       ( left-scalar-mul-vec-Ring r (left-scalar-mul-vec-Ring s v))
  associative-left-scalar-mul-vec-Ring r s empty-vec = refl
  associative-left-scalar-mul-vec-Ring r s (x ∷ v) =
    ap-binary _∷_
      ( associative-mul-Ring R r s x)
      ( associative-left-scalar-mul-vec-Ring r s v)

  associative-right-scalar-mul-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) (r s : type-Ring R) →
    Id ( right-scalar-mul-vec-Ring v (mul-Ring R r s))
       ( right-scalar-mul-vec-Ring (right-scalar-mul-vec-Ring v r) s)
  associative-right-scalar-mul-vec-Ring empty-vec r s = refl
  associative-right-scalar-mul-vec-Ring (x ∷ v) r s =
    ap-binary _∷_
      ( inv (associative-mul-Ring R x r s))
      ( associative-right-scalar-mul-vec-Ring v r s)

  associative-left-right-scalar-mul-vec-Ring :
    {n : ℕ} (r : type-Ring R) (v : vec-Ring R n) (s : type-Ring R) →
    Id ( right-scalar-mul-vec-Ring (left-scalar-mul-vec-Ring r v) s)
       ( left-scalar-mul-vec-Ring r (right-scalar-mul-vec-Ring v s))
  associative-left-right-scalar-mul-vec-Ring r empty-vec s = refl
  associative-left-right-scalar-mul-vec-Ring r (x ∷ v) s =
    ap-binary _∷_
      ( associative-mul-Ring R r x s)
      ( associative-left-right-scalar-mul-vec-Ring r v s)

  unit-law-left-scalar-mul-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (left-scalar-mul-vec-Ring (one-Ring R) v) v
  unit-law-left-scalar-mul-vec-Ring empty-vec = refl
  unit-law-left-scalar-mul-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-mul-Ring R x)
      ( unit-law-left-scalar-mul-vec-Ring v)

  unit-law-right-scalar-mul-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (right-scalar-mul-vec-Ring v (one-Ring R)) v
  unit-law-right-scalar-mul-vec-Ring empty-vec = refl
  unit-law-right-scalar-mul-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-mul-Ring R x)
      ( unit-law-right-scalar-mul-vec-Ring v)

  left-distributive-left-scalar-mul-add-vec-Ring :
    {n : ℕ} (r : type-Ring R) (v1 v2 : vec-Ring R n) →
    Id ( left-scalar-mul-vec-Ring r (add-vec-Ring R v1 v2))
       ( add-vec-Ring R (left-scalar-mul-vec-Ring r v1) (left-scalar-mul-vec-Ring r v2))
  left-distributive-left-scalar-mul-add-vec-Ring r empty-vec empty-vec = refl
  left-distributive-left-scalar-mul-add-vec-Ring r (x ∷ v1) (y ∷ v2) =
    ap-binary _∷_
      ( left-distributive-mul-add-Ring R r x y)
      ( left-distributive-left-scalar-mul-add-vec-Ring r v1 v2)

  right-distributive-left-scalar-mul-add-vec-Ring :
    {n : ℕ} (r s : type-Ring R) (v : vec-Ring R n) →
    Id ( left-scalar-mul-vec-Ring (add-Ring R r s) v)
       ( add-vec-Ring R (left-scalar-mul-vec-Ring r v) (left-scalar-mul-vec-Ring s v))
  right-distributive-left-scalar-mul-add-vec-Ring r s empty-vec = refl
  right-distributive-left-scalar-mul-add-vec-Ring r s (x ∷ v) =
    ap-binary _∷_
      ( right-distributive-mul-add-Ring R r s x)
      ( right-distributive-left-scalar-mul-add-vec-Ring r s v)

  left-distributive-right-scalar-mul-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) (r s : type-Ring R) →
    Id ( right-scalar-mul-vec-Ring v (add-Ring R r s))
       ( add-vec-Ring R (right-scalar-mul-vec-Ring v r) (right-scalar-mul-vec-Ring v s))
  left-distributive-right-scalar-mul-add-vec-Ring empty-vec r s = refl
  left-distributive-right-scalar-mul-add-vec-Ring (x ∷ v) r s =
    ap-binary _∷_
      ( left-distributive-mul-add-Ring R x r s)
      ( left-distributive-right-scalar-mul-add-vec-Ring v r s)

  right-distributive-right-scalar-mul-add-vec-Ring :
    {n : ℕ} (v1 v2 : vec-Ring R n) (r : type-Ring R) →
    Id ( right-scalar-mul-vec-Ring (add-vec-Ring R v1 v2) r)
       ( add-vec-Ring R (right-scalar-mul-vec-Ring v1 r) (right-scalar-mul-vec-Ring v2 r))
  right-distributive-right-scalar-mul-add-vec-Ring empty-vec empty-vec r = refl
  right-distributive-right-scalar-mul-add-vec-Ring (x1 ∷ v1) (x2 ∷ v2) r =
    ap-binary _∷_
      ( right-distributive-mul-add-Ring R x1 x2 r)
      ( right-distributive-right-scalar-mul-add-vec-Ring v1 v2 r)
```