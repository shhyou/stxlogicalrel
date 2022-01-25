# Modeling Simple Boolean Expressions

```agda
{-# OPTIONS --without-K --safe #-}

module BooleanOr where

open import Data.Bool.Base using (Bool ; true ; false)

infix 2 ∃
infix 22 _+_
infixr 18 _∧_
infixr 18 _∨_
```

## Warm Up: Basic Logic Connectives
### Implications 

```agda
--        ∀ P Q. P -> Q -> P
--        Λ P Q. λ (p : P) (q : Q). p
prop-f1 : (P : Set) → (Q : Set) → P → Q → P
prop-f1 = λ P Q → λ p q → p

prop-f2 : (P : Set) → (Q : Set) → (R : Set) →
          (Q → R) → (P → Q) → (P → R)
prop-f2 = λ P Q R g f x → g (f x)
```


## Conjunction

The constructor `AndProofs` has type `P → Q → P ∧ Q`.

```agda
data _∧_ (P : Set) (Q : Set) : Set where
    AndProofs :  P        →
                 Q        →
              -----------
                 P ∧ Q
```

```agda
and-left : ∀ P Q →
                P ∧ Q → P
and-left P Q (AndProofs p q) = p

and-right : ∀ P Q →
                P ∧ Q → Q
and-right P Q (AndProofs p q) = q
```


### Disjunction

```agda
data _∨_ (P : Set) (Q : Set) : Set where

    LeftProof  :        P       → 
                  -------------
                      P ∨ Q

    RightProof :        Q       → 
                  -------------
                      P ∨ Q

disjunction-elim : ∀ P Q → (R : Set) →
                      (P → R) →
                      (Q → R) →
                      (P ∨ Q → R)
disjunction-elim P Q R f g (LeftProof p)  = f p
disjunction-elim P Q R f g (RightProof q) = g q
```


## A Language for Boolean Expressions
### The Terms in the Language and Their Denotation

```agda
data LB : Set where
  tt  : LB
  ff  : LB
  _+_ : LB → LB → LB

expr1 = ff + ff
expr2 = ff + (tt + ff)
expr3 = (ff + (ff + (ff + tt))) + ff
```

```agda
sem : LB → Bool
sem tt = true
sem ff = false
sem (b₁ + b₂) with sem b₁
sem (b₁ + b₂) | true  = true
sem (b₁ + b₂) | false = sem b₂
```

### The Operational Semantics

```agda
data _Rᵣ_ : LB → LB → Set where

    R-true  : ∀ b →
                    ---------------------
                        (tt + b) Rᵣ tt

    R-false : ∀ b →
                    ---------------------
                        (ff + b) Rᵣ b
```

```agda
reduction1 : (tt + ff) Rᵣ tt
reduction1 = R-true ff

reduction2 : (ff + (tt + ff)) Rᵣ (tt + ff)
reduction2 = R-false (tt + ff)
```

```agda
data Value : LB → Set where
  V-tt : Value tt
  V-ff : Value ff

value-to-bool : ∀ {b} → Value b → Bool
value-to-bool {.tt} V-tt = true
value-to-bool {.ff} V-ff = false
```

```agda
prop-r1 : ∀ b₁ b₂ b →
            ((b₁ + b₂) Rᵣ b) → Value b₁
prop-r1 .tt b₂ .tt (R-true  .b₂) = V-tt
prop-r1 .ff b₂ .b₂ (R-false .b₂) = V-ff
```

```agda
data _⟶_ : LB → LB → Set where

    S-inc : ∀ {b₁ b₂} →
                      b₁ Rᵣ b₂         →
                  ----------------
                      b₁ ⟶ b₂

    S-plusL : ∀ {b₂ b₁ b₁′} →
                            b₁  ⟶ b₁′           →
                  -----------------------------
                      (b₁ + b₂) ⟶ (b₁′ + b₂)

reduction3 : (tt + ff) ⟶ tt
reduction3 = S-inc (R-true ff)

reduction4 : (tt + ff) + (ff + ff) ⟶ tt + (ff + ff)
reduction4 = S-plusL (S-inc (R-true ff))

data _⟶*_ : LB → LB → Set where
    TR-refl : ∀ {b} →
                        --------------
                           b ⟶* b

    TR-step : ∀ {b₂ b₁ b₃} →
                      b₁ ⟶  b₂        →
                      b₂ ⟶* b₃        →
                  ----------------
                      b₁ ⟶* b₃
```

### The Soundness of the Denotation

```agda
data _≡_ {A : Set} : A → A → Set where
  refl : ∀ a →
             ---------
               a ≡ a

prop-r2 : ∀ b₁ b₂ →
            ((b₁ + b₂) Rᵣ tt)  →  (b₁ ≡ tt) ∨ (b₂ ≡ tt)
prop-r2 .tt b2  (R-true .b2)  = LeftProof (refl tt)
prop-r2 .ff .tt (R-false .tt) = RightProof (refl tt)

prop-r3 : ∀ b₁ b₂ →
            ((b₁ + b₂) Rᵣ ff)  →  (b₁ ≡ ff) ∧ (b₂ ≡ ff)
prop-r3 .ff .ff (R-false .ff) = AndProofs (refl ff) (refl ff)
```

```agda
sem-equiv : ∀ {b b′} → (b ⟶ b′) → (sem b ≡ sem b′)
sem-equiv (S-inc (R-true b))   = refl true
sem-equiv (S-inc (R-false b′)) = refl (sem b′)
sem-equiv {b = b₁ + _} {b′ = b₁′ + b₂} (S-plusL b⟶b′)
  with sem b₁ | sem b₁′ | sem-equiv b⟶b′
... | true  | .true  | refl .true  = refl true
... | false | .false | refl .false = refl (sem b₂)

trans : ∀ {A} → {a : A} → {b : A} → {c : A} →
          a ≡ b → b ≡ c → a ≡ c
trans (refl a) (refl .a) = refl a

sem-sound1 : ∀ {b v} →
  (b ⟶* v) →
  (pf:v : Value v) →
  sem b ≡ value-to-bool pf:v
sem-sound1 TR-refl V-tt = refl true
sem-sound1 TR-refl V-ff = refl false
sem-sound1 (TR-step b⟶b2 b2⟶*v) pf:v
  with sem-equiv b⟶b2 | sem-sound1 b2⟶*v pf:v
... | sem-trans-eq | sem-v-eq = trans sem-trans-eq sem-v-eq
```

```agda
data ∃ (A : Set) (B : A → Set) : Set where
  witness : (a : A) → (b : B a) → ∃ A B

values-exist : ∃ LB (λ b → Value b)
values-exist = witness ff V-ff

split-reduction-sequence :
  ∀ {v b₁ b₂} →
    (b₁ + b₂ ⟶* v) →
    Value v →
    ∃ LB (λ v₁ →
           (b₁ ⟶* v₁) ∧ (Value v₁) ∧
           ((v₁ ≡ tt ∧ v ≡ tt) ∨
            (v₁ ≡ ff ∧ (b₂ ⟶* v))))
split-reduction-sequence (TR-step (S-inc (R-true _))  TR-refl)    pf:v =
  witness _ (AndProofs TR-refl (AndProofs V-tt (LeftProof (AndProofs (refl tt) (refl tt)))))
split-reduction-sequence (TR-step (S-inc (R-true _))  (TR-step (S-inc ()) _)) pf:v
split-reduction-sequence (TR-step (S-inc (R-false _)) b2⟶*v)    pf:v =
  witness _ (AndProofs TR-refl (AndProofs V-ff (RightProof (AndProofs (refl ff) b2⟶*v))))
split-reduction-sequence (TR-step (S-plusL b1⟶b1′)   b1′b2⟶*v) pf:v
  with split-reduction-sequence b1′b2⟶*v pf:v
... | witness v1 (AndProofs b1′⟶*v1 pf:others) =
  witness _ (AndProofs (TR-step b1⟶b1′ b1′⟶*v1) pf:others)

sem-sound2 : ∀ {b v} →
  (b ⟶* v) →
  (pf:v : Value v) →
  sem b ≡ value-to-bool pf:v
sem-sound2 TR-refl V-tt = refl true
sem-sound2 TR-refl V-ff = refl false
sem-sound2 (TR-step (S-inc (R-true b))  tt⟶*v) pf:v =
  sem-sound2 tt⟶*v pf:v
sem-sound2 (TR-step (S-inc (R-false b2)) b2⟶*v) pf:v =
  sem-sound2 b2⟶*v pf:v
sem-sound2 b⟶*v@(TR-step (S-plusL {b₁ = b1} _) _) pf:v
  with split-reduction-sequence b⟶*v pf:v
sem-sound2 b⟶*v@(TR-step (S-plusL {b₁ = b1} _) _) pf:v
  | witness v1 (AndProofs b1⟶*v1 (AndProofs pf:v1 pf:cases))
  with pf:v1 | sem b1 | sem-sound2 b1⟶*v1 pf:v1
sem-sound2 b⟶*v@(TR-step (S-plusL {b₁ = b1} _) _) pf:v
  | witness v1 (AndProofs b1⟶*v1 (AndProofs pf:v1 pf:cases))
  | V-tt | .(value-to-bool V-tt) | refl ._ with pf:cases | pf:v
... | LeftProof  (AndProofs _  (refl .tt)) | V-tt = refl true
... | RightProof (AndProofs () b2⟶*v)     | pf:v
sem-sound2 b⟶*v@(TR-step (S-plusL {b₁ = b1} _) _) pf:v
  | witness v1 (AndProofs b1⟶*v1 (AndProofs pf:v1 pf:cases))
  | V-ff | .(value-to-bool V-ff) | refl ._ with pf:cases
... | LeftProof  (AndProofs () v=tt)
... | RightProof (AndProofs _  b2⟶*v) = sem-sound2 b2⟶*v pf:v
```

### An Application

```agda
data HasT : LB → Set where
    HT-here :
               HasT tt

    HT-left : ∀ {b₁ b₂} →
                      HasT b₁        →
                ------------------
                  HasT (b₁ + b₂)

    HT-right : ∀ {b₁ b₂} →
                     HasT b₂        →
               ------------------
                 HasT (b₁ + b₂)
```

```agda
sem-hast-tt : ∀ {b} → HasT b → sem b ≡ true
sem-hast-tt HT-here = refl true
sem-hast-tt (HT-left  {b1} {b2} has-t) with sem b1 | sem-hast-tt has-t
... | .true | refl true = refl true
sem-hast-tt (HT-right {b1} {b2} has-t) with sem b1
... | true  = refl true
... | false = sem-hast-tt has-t


sym : ∀ {A} → {a : A} → {b : A} → a ≡ b → b ≡ a
sym (refl a) = refl a

goto-tt : ∀ {b v} →
             HasT b →
             (b ⟶* v) ∧ Value v →
             v ≡ tt
goto-tt has-t (AndProofs b⟶*v V-tt) = refl tt
goto-tt has-t (AndProofs b⟶*v V-ff)
  with trans (sym (sem-hast-tt has-t)) (sem-sound1 b⟶*v V-ff)
... | ()
```
