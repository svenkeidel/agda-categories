{-# OPTIONS --without-K --safe #-}
module Categories.Category.Core where

open import Level
open import Function.Base using (flip)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR


-- Mathematical Definition
-- -----------------------
-- A category consists of
--  * a collection of objects `A,B,C...` and a collection of arrows `(⇒)` between
--    objects called *hom-sets*,
--  * an identity arrow `id : A ⇒ A` for each object `A`,
--  * a composition operation `f ∘ g : A ⇒ C` for each arrow `f : B ⇒ C` and `g : A ⇒ B`.
--
-- Furthermore, identity and composition obey the following laws:
--  * Identity is left and right unital: `id ∘ f = f = f ∘ id` for each arrow `f : A ⇒ B`
--  * Composition is associative: `(f ∘ g) ∘ h = f ∘ (g ∘ h)` for each
--    `f : C ⇒ D`, `g : B ⇒ C`, `h : A ⇒ B`.
--
--
-- Examples
-- --------
-- Examples of categories can be found in the folder `Categories.Category.Instance`.
-- Notable examples include
--  * `Set`, the category of sets and functions (`Categories.Category.Instance.Sets`)
--  * `Poset`, the category of partial orderes sets and monotone functions (`Categories.Category.Instance.Cats`)
--  * `Cat`, the category of categories and functors (`Categories.Category.Instance.Cats`)
--
-- Implementation Details
-- ----------------------
-- Each category comes equipped with an equivalence relation `(≈)` on arrows.
-- This equivalence relation is used, instead of equality `(=)`, to describe the
-- laws of the category, e.g., `id ∘ f ≈ f`. This allows instances of categories
-- to describe how arrows should be compared. For example, the category `Set` of
-- sets and functions uses a point-wise equality on functions instead of `(=)`
-- to avoid the problem of functional extensionality.
--
-- To simplify the reasoning with this equivalence relation in Agda, the
-- relation forms a `Setoid` on hom-sets. Furthermore, the composition operation
-- respect the equivalence relation. In categorical terms, this means that a
-- category is enriched over the category of setoids.
record Category (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  eta-equality
  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : Rel Obj ℓ
    _≈_ : ∀ {A B} → Rel (A ⇒ B) e

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  field
    assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    -- We add a symmetric proof of associativity so that the opposite category of the
    -- opposite category is definitionally equal to the original category. See how
    -- `op` is implemented.
    sym-assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    -- We add a proof of "neutral" identity proof, in order to ensure the opposite of
    -- constant functor is definitionally equal to itself.
    identity² : ∀ {A} → id ∘ id {A} ≈ id {A}
    equiv     : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

  module Equiv {A B : Obj} = IsEquivalence (equiv {A} {B})

  open Equiv

  ∘-resp-≈ˡ : ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} → f ≈ h → f ∘ g ≈ h ∘ g
  ∘-resp-≈ˡ pf = ∘-resp-≈ pf refl

  ∘-resp-≈ʳ : ∀ {A B C} {f h : A ⇒ B} {g : B ⇒ C} → f ≈ h → g ∘ f ≈ g ∘ h
  ∘-resp-≈ʳ pf = ∘-resp-≈ refl pf

  hom-setoid : ∀ {A B} → Setoid _ _
  hom-setoid {A} {B} = record
    { Carrier       = A ⇒ B
    ; _≈_           = _≈_
    ; isEquivalence = equiv
    }

  -- Reasoning combinators.  _≈⟨_⟩_ and _≈˘⟨_⟩_ from SetoidR.
  -- Also some useful combinators for doing reasoning on _∘_ chains
  module HomReasoning {A B : Obj} where
    open SetoidR (hom-setoid {A} {B}) public
    -- open Equiv {A = A} {B = B} public

    infixr 4 _⟩∘⟨_ refl⟩∘⟨_
    infixl 5 _⟩∘⟨refl
    _⟩∘⟨_ : ∀ {M} {f h : M ⇒ B} {g i : A ⇒ M} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i
    _⟩∘⟨_ = ∘-resp-≈

    refl⟩∘⟨_ : ∀ {M} {f : M ⇒ B} {g i : A ⇒ M} → g ≈ i → f ∘ g ≈ f ∘ i
    refl⟩∘⟨_ = Equiv.refl ⟩∘⟨_

    _⟩∘⟨refl : ∀ {M} {f h : M ⇒ B} {g : A ⇒ M} → f ≈ h → f ∘ g ≈ h ∘ g
    _⟩∘⟨refl = _⟩∘⟨ Equiv.refl

    -- convenient inline versions
    infix 2 ⟺
    infixr 3 _○_
    ⟺ : {f g : A ⇒ B} → f ≈ g → g ≈ f
    ⟺ = Equiv.sym
    _○_ : {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
    _○_ = Equiv.trans

  op : Category o ℓ e
  op = record
    { Obj       = Obj
    ; _⇒_       = flip _⇒_
    ; _≈_       = _≈_
    ; _∘_       = flip _∘_
    ; id        = id
    ; assoc     = sym-assoc
    ; sym-assoc = assoc
    ; identityˡ = identityʳ
    ; identityʳ = identityˡ
    ; identity² = identity²
    ; equiv     = equiv
    ; ∘-resp-≈  = flip ∘-resp-≈
    }
