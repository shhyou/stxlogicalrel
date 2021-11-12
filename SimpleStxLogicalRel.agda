{-# OPTIONS --without-K #-}

module SimpleStxLogicalRel where

open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_ ; _≢_ ; refl)

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Bool using (Bool ; true ; false)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product
  using (Σ ; Σ-syntax ; ∃ ; ∃-syntax ; _,_ ; _×_)

open import Data.List using ([] ; _∷_ ; List)

infixr 25 _⇒_
infixl 30 ⟨_×_⟩

infix 60 `_
infix 50 _·_

infixr 50 _[_/0]

infix 15 _⟶_

data Ty : Set where
  TNat : Ty
  TBool : Ty
  _⇒_ : Ty → Ty → Ty
  ⟨_×_⟩ : Ty → Ty → Ty

Ctxt : Set
Ctxt = List Ty

data _∈/t_ : (τ : Ty) → (Γ : Ctxt) → Set where
  here/t : ∀ {Γ τ} →
    τ ∈/t (τ ∷ Γ)
  there/t : ∀ {Γ hd τ} →
    τ ∈/t Γ →
    τ ∈/t (hd ∷ Γ)

data _⊢_ :
  (Γ : Ctxt) →
  (τ : Ty) →
  Set where
    nat : ∀ {Γ} →
      (n : ℕ) →
      Γ ⊢ TNat

    _≐_ : ∀ {Γ} →
      Γ ⊢ TNat →
      Γ ⊢ TNat →
      Γ ⊢ TBool

    _∸_ : ∀ {Γ} →
      Γ ⊢ TNat →
      Γ ⊢ TNat →
      Γ ⊢ TNat

    bool : ∀ {Γ} →
      (b : Bool) →
      Γ ⊢ TBool

    `if : ∀ {Γ τ} →
      (ec : Γ ⊢ TBool) →
      (et : Γ ⊢ τ) →
      (ef : Γ ⊢ τ) →
      Γ ⊢ τ

    `_ : ∀ {Γ τ} →
      (y : τ ∈/t Γ) →
      Γ ⊢ τ

    ƛ_ : ∀ {Γ τa τr} →
      (τa ∷ Γ) ⊢ τr →
      Γ ⊢ (τa ⇒ τr)

    _·_ : ∀ {Γ τa τr} →
      (ef : Γ ⊢ τa ⇒ τr) →
      (ea : Γ ⊢ τa) →
      Γ ⊢ τr

    cons : ∀ {Γ τ1 τ2} →
      (e1 : Γ ⊢ τ1) →
      (e2 : Γ ⊢ τ2) →
      Γ ⊢ ⟨ τ1 × τ2 ⟩
    π₁ : ∀ {Γ τ1 τ2} →
      Γ ⊢ ⟨ τ1 × τ2 ⟩ →
      Γ ⊢ τ1

    π₂ : ∀ {Γ τ1 τ2} →
      Γ ⊢ ⟨ τ1 × τ2 ⟩ →
      Γ ⊢ τ2

ext : ∀ {Γ Γ′ τ} →
  (∀ {τ′} → τ′ ∈/t Γ → τ′ ∈/t Γ′) →
  ∀ {τ′} → τ′ ∈/t (τ ∷ Γ) → τ′ ∈/t (τ ∷ Γ′)
ext ren here/t = here/t
ext ren (there/t τ′∈Γ) = there/t (ren τ′∈Γ)

rename : ∀ {Γ′ Γ τ} →
  Γ ⊢ τ →
  (ren : ∀ {τ′} → τ′ ∈/t Γ → τ′ ∈/t Γ′) →
  Γ′ ⊢ τ
rename (nat n) ren        = nat n
rename (e1 ≐ e2) ren      = rename e2 ren ≐ rename e2 ren
rename (e1 ∸ e2) ren      = rename e1 ren ∸ rename e2 ren
rename (bool b) ren       = bool b
rename (`if ec et ef) ren = `if (rename ec ren) (rename et ren) (rename ef ren)
rename (` y) ren          = ` ren y
rename (ƛ e) ren          = ƛ rename e (ext ren)
rename (ef · ea) ren      = rename ef ren · rename ea ren
rename (cons e1 e2) ren   = cons (rename e1 ren) (rename e2 ren)
rename (π₁ e) ren         = π₁ (rename e ren)
rename (π₂ e) ren         = π₂ (rename e ren)

tsubst : ∀ {Γ′ Γ τ} →
  Γ ⊢ τ →
  (ϑ : ∀ {τ′} → τ′ ∈/t Γ → Γ′ ⊢ τ′) →
  Γ′ ⊢ τ
tsubst (nat n) ϑ        = nat n
tsubst (e1 ≐ e2) ϑ      = tsubst e2 ϑ ≐ tsubst e2 ϑ
tsubst (e1 ∸ e2) ϑ      = tsubst e1 ϑ ∸ tsubst e2 ϑ
tsubst (bool b) ϑ       = bool b
tsubst (`if ec et ef) ϑ = `if (tsubst ec ϑ) (tsubst et ϑ) (tsubst ef ϑ)
tsubst (` y) ϑ          = ϑ y
tsubst (ƛ e) ϑ          = ƛ tsubst e (λ where
  here/t → ` here/t
  (there/t τ∈Γ) → rename (ϑ τ∈Γ) there/t)
tsubst (ef · ea) ϑ      = tsubst ef ϑ · tsubst ea ϑ
tsubst (cons e1 e2) ϑ   = cons (tsubst e1 ϑ) (tsubst e2 ϑ)
tsubst (π₁ e) ϑ         = π₁ (tsubst e ϑ)
tsubst (π₂ e) ϑ         = π₂ (tsubst e ϑ)

_[_/0] : ∀ {τ τ′} →
  (τ ∷ []) ⊢ τ′ →
  (v : [] ⊢ τ) →
  [] ⊢ τ′
_[_/0] e v = tsubst e (λ where here/t → v)

data ⊢_∋_val :
  (τ : Ty) →
  (e : [] ⊢ τ) →
  Set where
    nat/v :
      (n : ℕ) →
      ⊢ TNat ∋ nat n val

    bool/v :
      (b : Bool) →
      ⊢ TBool ∋ bool b val

    ƛ/v_ : ∀ {τa τr} →
      (e : (τa ∷ []) ⊢ τr) →
      ⊢ (τa ⇒ τr) ∋ ƛ e val

    cons/v : ∀ {τ1 τ2 v1 v2} →
      (⊢v1 : ⊢ τ1 ∋ v1 val) →
      (⊢v2 : ⊢ τ2 ∋ v2 val) →
      ⊢ ⟨ τ1 × τ2 ⟩ ∋ cons v1 v2 val

data _⟶_ : ∀ {τ} →
  (e  : [] ⊢ τ) →
  (e′ : [] ⊢ τ) →
  Set where
    R-eqv? : ∀ {n1 n2} →
      (n1=n2 : Dec (n1 ≡ n2)) →
      nat n1 ≐ nat n2 ⟶ bool ⌊ n1=n2 ⌋

    R-sub : ∀ {n1 n2} →
      nat n1 ∸ nat n2 ⟶ nat (n1 Nat.∸ n2)

    R-then : ∀ {τ} →
      {et ef : [] ⊢ τ} →
      `if (bool true) et ef ⟶ et

    R-else : ∀ {τ} →
      {et ef : [] ⊢ τ} →
      `if (bool false) et ef ⟶ ef

    R-β : ∀ {τa τr} →
      {e : (τa ∷ []) ⊢ τr} →
      {v : [] ⊢ τa} →
      (ƛ e) · v ⟶ e [ v /0]

    R-π₁ : ∀ {τ1 τ2 v1 v2} →
      (⊢v1 : ⊢ τ1 ∋ v1 val) →
      (⊢v2 : ⊢ τ2 ∋ v2 val) →
      π₁ (cons v1 v2) ⟶ v1

    R-π₂ : ∀ {τ1 τ2 v1 v2} →
      (⊢v1 : ⊢ τ1 ∋ v1 val) →
      (⊢v2 : ⊢ τ2 ∋ v2 val) →
      π₂ (cons v1 v2) ⟶ v2

    E-≐l : ∀ {e1 e1′ e2} →
      e1 ⟶ e1′ →
      e1 ≐ e2 ⟶ e1′ ≐ e2

    E-≐r : ∀ {n e e′} →
      e ⟶ e′ →
      nat n ≐ e ⟶ nat n ≐ e′

    E-∸l : ∀ {e1 e1′ e2} →
      e1 ⟶ e1′ →
      e1 ∸ e2 ⟶ e1′ ∸ e2

    E-∸r : ∀ {n e e′} →
      e ⟶ e′ →
      nat n ∸ e ⟶ nat n ∸ e′

    E-if : ∀ {τ} →
      {ec ec′ : [] ⊢ TBool} →
      {et ef : [] ⊢ τ} →
      ec ⟶ ec′ →
      `if ec et ef ⟶ `if ec′ et ef

    E-appl : ∀ {τa τr} →
      {ef ef′ : [] ⊢ τa ⇒ τr} →
      {ea : [] ⊢ τa} →
      ef ⟶ ef′ →
      ef · ea ⟶ ef′ · ea

    E-appr : ∀ {τa τr} →
      {eb : (τa ∷ []) ⊢ τr} →
      {ea ea′ : [] ⊢ τa} →
      ea ⟶ ea′ →
      (ƛ eb) · ea ⟶ (ƛ eb) · ea′

    E-consl : ∀ {τ1 τ2} →
      {e1 e1′ : [] ⊢ τ1} →
      {e2 : [] ⊢ τ2} →
      e1 ⟶ e1′ →
      cons e1 e2 ⟶ cons e1′ e2

    E-consr : ∀ {τ1 τ2 v} →
      (⊢v : ⊢ τ1 ∋ v val) →
      {e e′ : [] ⊢ τ2} →
      e ⟶ e′ →
      cons v e ⟶ cons v e′

    E-π₁ : ∀ {τ1 τ2} →
      {e e′ : [] ⊢ ⟨ τ1 × τ2 ⟩} →
      e ⟶ e′ →
      π₁ e ⟶ π₁ e′

    E-π₂ : ∀ {τ1 τ2} →
      {e e′ : [] ⊢ ⟨ τ1 × τ2 ⟩} →
      e ⟶ e′ →
      π₂ e ⟶ π₂ e′

data _⟶*_ : ∀ {τ} →
  (e  : [] ⊢ τ) →
  (e′ : [] ⊢ τ) →
  Set where
    stop : ∀ {τ} →
      {e : [] ⊢ τ} →
      e ⟶* e

    step : ∀ {τ} →
      {e1 e2 e3 : [] ⊢ τ} →
      e1 ⟶* e2 →
      e2 ⟶ e3 →
      e1 ⟶* e3

Progress : ∀ {τ} →
  (e : [] ⊢ τ) →
  (⊢ τ ∋ e val) ⊎ (∃[ e′ ] e ⟶ e′)
Progress (nat n)        = inj₁ (nat/v n)
Progress (e1 ≐ e2)      with Progress e1
... | inj₂ (_ , e1⟶e1′) = inj₂ (_ , E-≐l e1⟶e1′)
... | inj₁ (nat/v n1)   with Progress e2
... | inj₂ (_ , e2⟶e2′) = inj₂ (_ , E-≐r e2⟶e2′)
... | inj₁ (nat/v n2)   = inj₂ (_ , R-eqv? (n1 Nat.≟ n2))
Progress (e1 ∸ e2)      with Progress e1
... | inj₂ (_ , e1⟶e1′) = inj₂ (_ , E-∸l e1⟶e1′)
... | inj₁ (nat/v n1)   with Progress e2
... | inj₂ (_ , e2⟶e2′) = inj₂ (_ , E-∸r e2⟶e2′)
... | inj₁ (nat/v n2)   = inj₂ (_ , R-sub)
Progress (bool b)       = inj₁ (bool/v b)
Progress (`if ec et ef) with Progress ec
... | inj₂ (_ , ec⟶ec′) = inj₂ (_ , E-if ec⟶ec′)
... | inj₁(bool/v true) = inj₂ (_ , R-then)
... | inj₁(bool/v false)= inj₂ (_ , R-else)
Progress (ƛ e)          = inj₁ (ƛ/v e)
Progress (ef · ea)      with Progress ef
... | inj₂ (_ , ef⟶ef′) = inj₂ (_ , E-appl ef⟶ef′)
... | inj₁ (ƛ/v eb)     with Progress ea
... | inj₂ (_ , ea⟶ea′) = inj₂ (_ , E-appr ea⟶ea′)
... | inj₁ ⊢v2          = inj₂ (_ , R-β)
Progress (cons e1 e2)   with Progress e1
... | inj₂ (_ , e1⟶e1′) = inj₂ (_ , E-consl e1⟶e1′)
... | inj₁ ⊢v1          with Progress e2
... | inj₂ (_ , e2⟶e2′) = inj₂ (_ , E-consr ⊢v1 e2⟶e2′)
... | inj₁ ⊢v2          = inj₁ (cons/v ⊢v1 ⊢v2)
Progress (π₁ e)         with Progress e
... | inj₁ (cons/v ⊢v1 ⊢v2) = inj₂ (_ , R-π₁ ⊢v1 ⊢v2)
... | inj₂ (_ , e⟶e′) = inj₂ (_ , E-π₁ e⟶e′)
Progress (π₂ e)         with Progress e
... | inj₁ (cons/v ⊢v1 ⊢v2) = inj₂ (_ , R-π₂ ⊢v1 ⊢v2)
... | inj₂ (_ , e⟶e′) = inj₂ (_ , E-π₂ e⟶e′)
