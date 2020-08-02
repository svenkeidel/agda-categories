{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Core where

open import Level

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

-- Mathematical Definition
-- -----------------------
-- A functor `F: C ⇒ D` is a mapping between two categories `C` and `D`. It
-- consists of
--  * a mapping `F₀` from objects in `C` to objects in `D`,
--  * a mapping `F₁ : C[X,Y] → D[F₀ X, F₀ Y]` of arrows in `C` to arrows in `D`
--    for every object `X` and `Y` in `C`.
--
-- These mappings have to obey the following laws:
--  * `F` preserves identities: `F₁(id_X) = id_F₀(X)` for all objects `X` in `C`.
--  * `F` preserves composition: `F₁(f ∘ g) = F₁(f) ∘ F₁(g)` for each `f: Y ⇒ Z`
--    and `g: X ⇒ Y` in `C`.
--
-- Further reading:
--  * https://en.wikipedia.org/wiki/Functor
--  * https://ncatlab.org/nlab/show/functor
--
--
-- Examples
-- --------
-- Examples of functors can be found in the folder `Categories.Functor`.
-- Notable examples include
--  * the identity functor `Id: C ⇒ C` from a category to itself (`Categories.Functor`),
--  * the composition functor `F∘G: C ⇒ E`, that takes two functors `F: D ⇒ E`
--    and `G: C ⇒ D` and calculates their composition (`Categories.Functor`),
--  * the forgetful functor `U: Poset ⇒ Set`, that maps partially ordered sets to
--    their underlying sets.
--
--
-- Implementation Details
-- ----------------------
-- To simplify reasoning, each category comes equipped with an equivalence
-- relation `(≈)` on arrows, which forms a setoid (see `Categories.Category.Core`).
-- Therefore, to allow rewriting ≈-equations with a functor `F: C ⇒ D`, the
-- arrow mapping F₁ of needs to respect the equivalence relations of `C` and
-- `D`. More formally, if `f ≈ g` then `F₁ f ≈ F₁ g` for all `f, g: C[A,B]`.
record Functor (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  eta-equality
  private module C = Category C
  private module D = Category D

  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} (f : C [ A , B ]) → D [ F₀ A , F₀ B ]

    identity     : ∀ {A} → D [ F₁ (C.id {A}) ≈ D.id ]
    homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
                     D [ F₁ (C [ g ∘ f ]) ≈ D [ F₁ g ∘ F₁ f ] ]
    F-resp-≈     : ∀ {A B} {f g : C [ A , B ]} → C [ f ≈ g ] → D [ F₁ f ≈ F₁ g ]

  -- nice shorthands
  ₀ = F₀
  ₁ = F₁

  op : Functor C.op D.op
  op = record
    { F₀           = F₀
    ; F₁           = F₁
    ; identity     = identity
    ; homomorphism = homomorphism
    ; F-resp-≈     = F-resp-≈
    }
