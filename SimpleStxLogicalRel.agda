{-# OPTIONS --without-K #-}

module SimpleStxLogicalRel where

open import Relation.Nullary
  using (¬_ ; Dec ; _because_ ; yes ; no ; Irrelevant)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_ ; _≢_ ; refl ; cong ; sym ; subst)

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product
  using (Σ ; Σ-syntax ; ∃ ; ∃-syntax ; proj₁ ; proj₂ ; _,_ ; _,′_ ; _×_ ; -,_)

open import Data.List.Base using ([] ; _∷_ ; List)

open import Function.Base using (_∘_)

infixr 25 _⇒_
infixl 30 ⟨_×_⟩

infix 60 `_
infix 50 _·_

infixr 50 _[_/0]

infix 15 _⟶_

truth-irrelevant : ∀ {P : Set} →
  (dec1 dec2 : Dec P) →
  ⌊ dec1 ⌋ ≡ ⌊ dec2 ⌋
truth-irrelevant (false because ofp1) (false because ofp2) = refl
truth-irrelevant (no ¬p)              (yes p)              = ⊥-elim (¬p p)
truth-irrelevant (yes p)              (no ¬p)              = ⊥-elim (¬p p)
truth-irrelevant (true because ofp1)  (true because ofp2)  = refl

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
rename (e1 ≐ e2) ren      = rename e1 ren ≐ rename e2 ren
rename (e1 ∸ e2) ren      = rename e1 ren ∸ rename e2 ren
rename (bool b) ren       = bool b
rename (`if ec et ef) ren = `if (rename ec ren) (rename et ren) (rename ef ren)
rename (` y) ren          = ` ren y
rename (ƛ e) ren          = ƛ rename e (ext ren)
rename (ef · ea) ren      = rename ef ren · rename ea ren
rename (cons e1 e2) ren   = cons (rename e1 ren) (rename e2 ren)
rename (π₁ e) ren         = π₁ (rename e ren)
rename (π₂ e) ren         = π₂ (rename e ren)

term-ext : ∀ {τ Γ Γ′} →
  (ϑ : ∀ {τ′} → τ′ ∈/t Γ → Γ′ ⊢ τ′) →
  ∀ {τ′} → τ′ ∈/t (τ ∷ Γ) → (τ ∷ Γ′) ⊢ τ′
term-ext ϑ here/t        = ` here/t
term-ext ϑ (there/t τ∈Γ) = rename (ϑ τ∈Γ) there/t

term-subst : ∀ {Γ′ Γ τ} →
  Γ ⊢ τ →
  (ϑ : ∀ {τ′} → τ′ ∈/t Γ → Γ′ ⊢ τ′) →
  Γ′ ⊢ τ
term-subst (nat n) ϑ        = nat n
term-subst (e1 ≐ e2) ϑ      = term-subst e1 ϑ ≐ term-subst e2 ϑ
term-subst (e1 ∸ e2) ϑ      = term-subst e1 ϑ ∸ term-subst e2 ϑ
term-subst (bool b) ϑ       = bool b
term-subst (`if ec et ef) ϑ = `if (term-subst ec ϑ) (term-subst et ϑ) (term-subst ef ϑ)
term-subst (` y) ϑ          = ϑ y
term-subst (ƛ e) ϑ          = ƛ term-subst e (term-ext ϑ)
term-subst (ef · ea) ϑ      = term-subst ef ϑ · term-subst ea ϑ
term-subst (cons e1 e2) ϑ   = cons (term-subst e1 ϑ) (term-subst e2 ϑ)
term-subst (π₁ e) ϑ         = π₁ (term-subst e ϑ)
term-subst (π₂ e) ϑ         = π₂ (term-subst e ϑ)

singleton-context : ∀ {τ} → [] ⊢ τ → ∀ {τ′} → τ′ ∈/t (τ ∷ []) → [] ⊢ τ′
singleton-context e here/t = e

_[_/0] : ∀ {τ τ′} →
  (τ ∷ []) ⊢ τ′ →
  (v : [] ⊢ τ) →
  [] ⊢ τ′
_[_/0] e v = term-subst e (singleton-context v)

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

    R-β : ∀ {τa τr v} →
      {e  : (τa ∷ []) ⊢ τr} →
      (⊢v : ⊢ τa ∋ v val) →
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
      e1 ⟶ e2 →
      e2 ⟶* e3 →
      e1 ⟶* e3

⟶*-++ : ∀ {τ} →
  {e1 e2 e3 : [] ⊢ τ} →
  (e1 ⟶* e2) →
  (e2 ⟶* e3) →
  (e1 ⟶* e3)
⟶*-++ stop                e2⟶*e3 = e2⟶*e3
⟶*-++ (step e1⟶e4 e4⟶*e2) e2⟶*e3 = step e1⟶e4 (⟶*-++ e4⟶*e2 e2⟶*e3)

value-does-not-reduce :
  ∀ {τ v e} →
    ⊢ τ ∋ v val →
    ¬ (v ⟶ e)
value-does-not-reduce (cons/v ⊢v1 ⊢v2) (E-consl v1⟶e) =
  value-does-not-reduce ⊢v1 v1⟶e
value-does-not-reduce (cons/v ⊢v1 ⊢v2) (E-consr ⊢v1′ v2⟶e) =
  value-does-not-reduce ⊢v2 v2⟶e

value-does-not-reduce* :
  ∀ {τ v e} →
    ⊢ τ ∋ v val →
    (v→*e : v ⟶* e) →
    Σ (v ≡ e) λ where refl → v→*e ≡ stop
value-does-not-reduce* ⊢v stop =
  refl , refl
value-does-not-reduce* ⊢v (step v⟶e e⟶*e′)
  with value-does-not-reduce ⊢v v⟶e
... | ()

⟶-is-deterministic :
  ∀ {τ e1 e2} →
    {e : [] ⊢ τ} →
    e ⟶ e1 →
    e ⟶ e2 →
    e1 ≡ e2
⟶-is-deterministic (R-eqv? n1=n2) (R-eqv? n1=n2′) =
  cong bool (truth-irrelevant n1=n2 n1=n2′)
⟶-is-deterministic R-sub  R-sub       = refl
⟶-is-deterministic R-then R-then      = refl
⟶-is-deterministic R-else R-else      = refl
⟶-is-deterministic (R-β ⊢v) (R-β ⊢v′) =
  refl
⟶-is-deterministic (R-β ⊢v) (E-appr v⟶ea′) =
  ⊥-elim (value-does-not-reduce ⊢v v⟶ea′)
⟶-is-deterministic                   (R-π₁ ⊢v1 ⊢v2)              (R-π₁ ⊢v1′ ⊢v2′) = refl
⟶-is-deterministic                   (R-π₁ ⊢v1 ⊢v2)              (E-π₁ v1v2⟶e′) =
  ⊥-elim (value-does-not-reduce (cons/v ⊢v1 ⊢v2) v1v2⟶e′)
⟶-is-deterministic                   (R-π₂ ⊢v1 ⊢v2)              (R-π₂ ⊢v1′ ⊢v2′) = refl
⟶-is-deterministic                   (R-π₂ ⊢v1 ⊢v2)              (E-π₂ v1v2⟶e′) =
  ⊥-elim (value-does-not-reduce (cons/v ⊢v1 ⊢v2) v1v2⟶e′)
⟶-is-deterministic {e = _ ≐ e2}      (E-≐l e1⟶e1′)               (E-≐l e1⟶e2′) =
  cong (_≐ e2) (⟶-is-deterministic e1⟶e1′ e1⟶e2′)
⟶-is-deterministic {e = nat n ≐ _}   (E-≐r {e = e1} e1⟶e′)       (E-≐r e1⟶e′′) =
  cong (nat n ≐_) (⟶-is-deterministic e1⟶e′ e1⟶e′′)
⟶-is-deterministic {e2 = _ ∸ e2}     (E-∸l e1⟶e′)                (E-∸l e1⟶e′′) =
  cong (_∸ e2) (⟶-is-deterministic e1⟶e′ e1⟶e′′)
⟶-is-deterministic {e = nat n ∸ _}   (E-∸r {e = e1} e1⟶e′)       (E-∸r e1⟶e′′) =
  cong (nat n ∸_) (⟶-is-deterministic e1⟶e′ e1⟶e′′)
⟶-is-deterministic {e = `if _ et ef} (E-if ec⟶ec′)               (E-if ec⟶ec′′) =
  cong (λ ec → `if ec et ef) (⟶-is-deterministic ec⟶ec′ ec⟶ec′′)
⟶-is-deterministic {e = _ · ea}      (E-appl ef⟶e′)              (E-appl ef⟶ef′) =
  cong (_· ea) (⟶-is-deterministic ef⟶e′ ef⟶ef′)
⟶-is-deterministic {e = v · _}       (E-appr v⟶e′)               (R-β ⊢v) =
  ⊥-elim (value-does-not-reduce ⊢v v⟶e′)
⟶-is-deterministic {e = v · _}       (E-appr ea⟶e′)              (E-appr ea⟶e′′) =
  cong (v ·_) (⟶-is-deterministic ea⟶e′ ea⟶e′′)
⟶-is-deterministic {e = cons _ e2}   (E-consl e1⟶e1′)            (E-consl e1⟶e2′) =
  cong (λ e1 → cons e1 e2) (⟶-is-deterministic e1⟶e1′ e1⟶e2′)
⟶-is-deterministic {e = cons _ e2}   (E-consl v⟶e′)              (E-consr ⊢v e2⟶e′′) =
  ⊥-elim (value-does-not-reduce ⊢v v⟶e′)
⟶-is-deterministic {e = cons v _}    (E-consr ⊢v {e = e2} e2⟶e′) (E-consl v⟶e′′) =
  ⊥-elim (value-does-not-reduce ⊢v v⟶e′′)
⟶-is-deterministic {e = cons v _}    (E-consr ⊢v {e = e2} e2⟶e′) (E-consr ⊢v′ e2⟶e′′) =
  cong (cons v) (⟶-is-deterministic e2⟶e′ e2⟶e′′)
⟶-is-deterministic                   (E-π₁ v1v2⟶e′)              (R-π₁ ⊢v1 ⊢v2) =
  ⊥-elim (value-does-not-reduce (cons/v ⊢v1 ⊢v2) v1v2⟶e′)
⟶-is-deterministic                   (E-π₁ e⟶e′)                 (E-π₁ e⟶e′′) =
  cong π₁ (⟶-is-deterministic e⟶e′ e⟶e′′)
⟶-is-deterministic                   (E-π₂ v1v2⟶e′)              (R-π₂ ⊢v1 ⊢v2) =
  ⊥-elim (value-does-not-reduce (cons/v ⊢v1 ⊢v2) v1v2⟶e′)
⟶-is-deterministic                   (E-π₂ e⟶e′)                 (E-π₂ e⟶e′′) =
  cong π₂ (⟶-is-deterministic e⟶e′ e⟶e′′)

⟶*-is-deterministic : ∀ {τ} →
  {e e1 e2 : [] ⊢ τ} →
  e ⟶* e1 →
  e ⟶* e2 →
  (e1 ⟶* e2) ⊎ (e2 ⟶* e1)
⟶*-is-deterministic stop               e⟶*e2 = inj₁ e⟶*e2
⟶*-is-deterministic (step e⟶e3 e3⟶*e1) stop  = inj₂ (step e⟶e3 e3⟶*e1)
⟶*-is-deterministic (step e⟶e3 e3⟶*e1) (step e⟶e4 e4⟶*e2)
  with ⟶-is-deterministic e⟶e3 e⟶e4
... | refl = ⟶*-is-deterministic e3⟶*e1 e4⟶*e2

⟶*v-is-deterministic : ∀ {τ v1 v2} →
  {e : [] ⊢ τ} →
  (⊢v1 : ⊢ τ ∋ v1 val) →
  (⊢v1 : ⊢ τ ∋ v2 val) →
  e ⟶* v1 →
  e ⟶* v2 →
  v1 ≡ v2
⟶*v-is-deterministic ⊢v1 ⊢v2 e⟶*v1 e⟶*v2 with ⟶*-is-deterministic e⟶*v1 e⟶*v2
... | inj₁ stop = refl
... | inj₁ (step v1⟶e1 e1⟶*v2) = ⊥-elim (value-does-not-reduce ⊢v1 v1⟶e1)
... | inj₂ stop = refl
... | inj₂ (step v2⟶e2 e2⟶*v1) = ⊥-elim (value-does-not-reduce ⊢v2 v2⟶e2)

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
... | inj₁ ⊢v2          = inj₂ (_ , R-β ⊢v2)
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
