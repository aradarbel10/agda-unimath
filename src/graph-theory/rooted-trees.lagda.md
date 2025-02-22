---
title: Rooted trees
---

```agda
module graph-theory.rooted-trees where

open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs

open import graph-theory.trails-undirected-graphs
open import graph-theory.trees
open import graph-theory.undirected-graphs
```

## Idea

A rooted tree is a tree equipped with a marked node. The marked node is called the **root** of the tree.

## Definition

```agda
Rooted-Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Rooted-Tree l1 l2 = Σ (Tree l1 l2) node-Tree

module _
  {l1 l2 : Level} (T : Rooted-Tree l1 l2)
  where

  tree-Rooted-Tree : Tree l1 l2
  tree-Rooted-Tree = pr1 T

  undirected-graph-Rooted-Tree : Undirected-Graph l1 l2
  undirected-graph-Rooted-Tree = undirected-graph-Tree tree-Rooted-Tree

  node-Rooted-Tree : UU l1
  node-Rooted-Tree = node-Tree tree-Rooted-Tree

  root-Rooted-Tree : node-Rooted-Tree
  root-Rooted-Tree = pr2 T

  trail-to-root-Rooted-Tree :
    (x : node-Rooted-Tree) →
    trail-Undirected-Graph undirected-graph-Rooted-Tree x root-Rooted-Tree
  trail-to-root-Rooted-Tree x =
    standard-trail-Tree tree-Rooted-Tree x root-Rooted-Tree

  height-node-Rooted-Tree : node-Rooted-Tree → ℕ
  height-node-Rooted-Tree x =
    length-trail-Undirected-Graph
      ( undirected-graph-Rooted-Tree)
      ( trail-to-root-Rooted-Tree x)

  node-of-height-one-Rooted-Tree : UU l1
  node-of-height-one-Rooted-Tree =
    Σ node-Rooted-Tree (λ x → is-one-ℕ (height-node-Rooted-Tree x))
```

## Properties

### The type of rooted trees is equivalent to the type of forests of rooted trees

```agda
Forest-Rooted-Trees : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Forest-Rooted-Trees l1 l2 l3 = Σ (UU l1) (λ X → X → Rooted-Tree l2 l3)

module _
  {l1 l2 l3 : Level} (F : Forest-Rooted-Trees l1 l2 l3)
  where

  indexing-type-Forest-Rooted-Trees : UU l1
  indexing-type-Forest-Rooted-Trees = pr1 F

  family-of-rooted-trees-Forest-Rooted-Trees :
    indexing-type-Forest-Rooted-Trees → Rooted-Tree l2 l3
  family-of-rooted-trees-Forest-Rooted-Trees = pr2 F

  node-rooted-tree-Forest-Rooted-Trees : UU (l1 ⊔ l2)
  node-rooted-tree-Forest-Rooted-Trees =
    ( Σ indexing-type-Forest-Rooted-Trees
      ( λ x →
        node-Rooted-Tree (family-of-rooted-trees-Forest-Rooted-Trees x))) +
    ( unit)

  unordered-pair-of-nodes-rooted-tree-Forest-Rooted-Trees :
    UU (lsuc lzero ⊔ l1 ⊔ l2)
  unordered-pair-of-nodes-rooted-tree-Forest-Rooted-Trees =
    unordered-pair node-rooted-tree-Forest-Rooted-Trees
```
