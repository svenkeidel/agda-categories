{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.Core where

open import Level

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D E : Category o ℓ e

-- Mathematical Definition
-- -----------------------
-- A natural transformation `η: F ⇒ G` is a mapping between two functors
-- `F, G: C ⇒ D`. It consists of a family of arrows `η_X: FX ⇒ GX` in `D`, for
-- each object `X` in `C`, such that the following diagram commutes for each `f:
-- X ⇒ Y` in `C`:
--          η_X
--     FX ------> GX
--      |          |
--    Ff|          | Gf
--      |          |
--      v   η_Y    v
--     FY ------> GY
--
-- In other words, a natural transformation connects the image of `F` to the
-- image of `G` in a coherent way.
--
-- Diagramatically, natural transformations are notated as follows:
--          C
--         / \
--        / η \
--     F | ==> | G
--        \   /
--         \ /
--          D
--
-- Further reading:
--  * https://en.wikipedia.org/wiki/Natural_transformation
--  * https://ncatlab.org/nlab/show/natural+transformation
--
--
-- Examples
-- --------
-- Examples of functors can be found in the folder `Categories.NaturalTransformation`.
-- Notable examples of natural transformations include
--  * the identity transformation `id: F ⇒ F` from a functor to itself,
--    (`Categories.NaturalTransformation.Core`),
--  * the vertical composition `η∘ᵥθ: F ⇒ H` of two natural transformations
--    `η: G ⇒ H` and `θ: F ⇒ G` (`Categories.NaturalTransformation.Core`).
--  * the horizontal composition `η∘ₕθ: FG ⇒ HI` of two natural transformations
--    `η: F ⇒ H` and `θ: G ⇒ I` (`Categories.NaturalTransformation.Core`).
record NaturalTransformation {C : Category o ℓ e}
                             {D : Category o′ ℓ′ e′}
                             (F G : Functor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
  eta-equality
  private
    module F = Functor F
    module G = Functor G
  open F using (F₀; F₁)
  open Category D hiding (op)

  field
    η           : ∀ X → D [ F₀ X , G.F₀ X ]
    commute     : ∀ {X Y} (f : C [ X , Y ]) → η Y ∘ F₁ f ≈ G.F₁ f ∘ η X
    -- We introduce an extra proof to ensure the opposite of the opposite of a natural
    -- transformation is definitionally equal to itself.
    sym-commute : ∀ {X Y} (f : C [ X , Y ]) → G.F₁ f ∘ η X ≈ η Y ∘ F₁ f

  op : NaturalTransformation G.op F.op
  op = record
    { η           = η
    ; commute     = sym-commute
    ; sym-commute = commute
    }

-- Just like `Category`, we introduce a helper definition to ease the actual
-- construction of a natural transformation.
record NTHelper {C : Category o ℓ e}
                {D : Category o′ ℓ′ e′}
                (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G = Functor G
  open Functor F using (F₀; F₁)
  open Category D hiding (op)
  field
    η           : ∀ X → D [ F₀ X , G.F₀ X ]
    commute     : ∀ {X Y} (f : C [ X , Y ]) → η Y ∘ F₁ f ≈ G.F₁ f ∘ η X

ntHelper : ∀ {F G : Functor C D} → NTHelper F G → NaturalTransformation F G
ntHelper {D = D} α = record
  { η           = η
  ; commute     = commute
  ; sym-commute = λ f → Equiv.sym (commute f)
  }
  where open NTHelper α
        open Category D

-- Don't use ntHelper as it produces non-reduction in other places
-- and be pedantic about arguments too, this helps inference too.
id : ∀ {F : Functor C D} → NaturalTransformation F F
id {D = D} {F} = record
  { η = λ _ → D.id
  ; commute = λ f → id-comm-sym {f = Functor.F₁ F f}
  ; sym-commute = λ f → id-comm {f = Functor.F₁ F f}
  }
  where
  module D = Category D
  open MR D

infixr 9 _∘ᵥ_ _∘ₕ_ _∘ˡ_ _∘ʳ_

-- "Vertical composition"
_∘ᵥ_ : ∀ {F G H : Functor C D} →
         NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
_∘ᵥ_ {C = C} {D = D} {F} {G} {H} X Y = record
  { η       = λ q → D [ X.η q ∘ Y.η q ]
  ; commute = λ f → glue (X.commute f) (Y.commute f)
  ; sym-commute = λ f → Category.Equiv.sym D (glue (X.commute f) (Y.commute f))
  }
  where module X = NaturalTransformation X
        module Y = NaturalTransformation Y
        open MR D

-- "Horizontal composition"
_∘ₕ_ : ∀ {F G : Functor C D} {H I : Functor D E} →
         NaturalTransformation H I → NaturalTransformation F G → NaturalTransformation (H ∘F F) (I ∘F G)
_∘ₕ_ {E = E} {F} {I = I} Y X = ntHelper record
  { η = λ q → E [ I₁ (X.η q) ∘ Y.η (F.F₀ q) ]
  ; commute = λ f → glue ([ I ]-resp-square (X.commute f)) (Y.commute (F.F₁ f))
  }
  where module F = Functor F
        module X = NaturalTransformation X
        module Y = NaturalTransformation Y
        open Functor I renaming (F₀ to I₀; F₁ to I₁)
        open MR E

_∘ˡ_ : ∀ {G H : Functor C D} (F : Functor D E) → NaturalTransformation G H → NaturalTransformation (F ∘F G) (F ∘F H)
_∘ˡ_ F α = record
  { η           = λ X → F₁ (η X)
  ; commute     = λ f → [ F ]-resp-square (commute f)
  ; sym-commute = λ f → [ F ]-resp-square (sym-commute f)
  }
  where open Functor F
        open NaturalTransformation α

_∘ʳ_ : ∀ {G H : Functor D E} → NaturalTransformation G H → (F : Functor C D) → NaturalTransformation (G ∘F F) (H ∘F F)
_∘ʳ_ {D = D} {E = E} {G = G} {H = H} α F = record
  { η           = λ X → η (F₀ X)
  ; commute     = λ f → commute (F₁ f)
  ; sym-commute = λ f → sym-commute (F₁ f)
  }
  where open Functor F
        open NaturalTransformation α

id∘id⇒id : {C : Category o ℓ e} → NaturalTransformation {C = C} {D = C} (idF ∘F idF) idF
id∘id⇒id {C = C} = record
  { η           = λ _ → Category.id C
  ; commute     = λ f → MR.id-comm-sym C {f = f}
  ; sym-commute = λ f → MR.id-comm C {f = f}
  }

id⇒id∘id : {C : Category o ℓ e} → NaturalTransformation {C = C} {D = C} idF (idF ∘F idF)
id⇒id∘id {C = C} = record
  { η           = λ _ → Category.id C
  ; commute     = λ f → MR.id-comm-sym C {f = f}
  ; sym-commute = λ f → MR.id-comm C {f = f}
  }

module _ {F : Functor C D} where
  open Category.HomReasoning D
  open Functor F
  open Category D
  open MR D
  private module D = Category D

  F⇒F∘id : NaturalTransformation F (F ∘F idF)
  F⇒F∘id = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

  F⇒id∘F : NaturalTransformation F (idF ∘F F)
  F⇒id∘F = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

  F∘id⇒F : NaturalTransformation (F ∘F idF) F
  F∘id⇒F = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

  id∘F⇒F : NaturalTransformation (idF ∘F F) F
  id∘F⇒F = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }
